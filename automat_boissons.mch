/* automat_boissons
 * Author: 
 * Creation date: 05/03/17
 */
 
 /* /////////////////////////////////////////////////
 // J'ai bien vu qu'il y avait plein d'erreur que
 // je corrigerais avec la correction mais je rend
 // ce devoir déjà pour m'être confronté au question
 // de l'énoncer.
 // C'était pour m'excuser de ne pas avoir rendu
 // quelque chose de très propre.
 *//////////////////////////////////////////////////
MACHINE
    automat_boissons
    
SETS
    ETAGERES;                       // l'ensemble des étagères
    CASIERS;                        // L'ensemble des casiers 
    BOISSONS;                       // l'ensemble des boissons
    PRIX;                           // l'ensemble de tout les prix
    MONNAIES;                       //l'ensemble de la monnaie
    CAISSES;                        //l'ensemble des caisse
    DISPO = {oui,non};              //l'ensemble des disponibilité
    STATUT = {service,hs}           //l'ensemble de tout les statuts de la machine
    
CONSTANTS
    MAX_ETAGERE, // le nombre max d'étagères
    MAX_CASIER,  // le nombre max de casier par étagères
    MAX_CAISSE   // le nombre max de pièces dans la caisse
    
PROPERTIES
    MAX_ETAGERE = 8 &
    MAX_CASIER = 10 &
    MAX_CAISSE = 500
    
    
VARIABLES
    etagere,
    casier,
    boisson,
    prix,
    monnaies_entre,
    monnaies_rendu,
    caisse,
    dispo, // nombre de boisson encore disponible
    statut
    
INVARIANT
    etagere <: ETAGERES &           // Les étagères du distributeur
    casier : etagere <-> CASIERS &  // les casier des étagères 
    boisson : NAT1 +-> etagere &    // les boissons dans les étagères
    prix : etagere <-> PRIX &       // le prix de chaque boisson
    monnaies_entre <: MONNAIES &   // le monnaies introduite
    monnaies_rendu <: MONNAIES &   //la monnaies rendu
    caisse <: CAISSES &             // l'argent de la caisse
    dispo : etagere --> DISPO &     // la disponibilité de la boisson
    statut : STATUT &               // le statu de la machine
    
    
    !(bois).(bois : boisson => card(dispo|> {bois}) <= MAX_CASIER)& //Le nombre de boisson ne peut pas dépasser le nombre de casier
    caisse <= MAX_CAISSE & // la caisse a un nombre limite de pièces
    monnaies_rendu <= monnaies_entre //on ne peut pas rendre plus de monnaie que ne nombre introduit
    
            
INITIALISATION
    etagere := {} ||
    casier := {} ||
    boisson := {} ||
    prix := {} ||
    dispo := {non} ||
    caisse := {} ||
    monnaies_entre := {} ||
    monnaies_rendu := {} ||
    statut := {service}
    
OPERATIONS
        
    /*permet de fixer les prix des boissons installées sur une étagère donnée*/
    setPriceOfShelf(px, et) =
        PRE
            px : prix &
            et : etagere
        THEN
            etagere := etagere \/ {et |-> px}
        END;
        
    /*permet de déposer une boisson sur une étagère donnée*/
    putDrinkOnShelf(et) =
        PRE
            et : etagere &
            et <= MAX_ETAGERE
        THEN
            ANY bo WHERE bo : NAT1 & bo /: dom(boisson)
            THEN
                boisson := boisson \/ {bo |-> et} //&
                //dispo := {oui}
            END
        END;
        
    /*permet d'insérer un nombre de pièces donné dans le distributeur*/
    insertMoney(nb) =
        PRE
            nb : monnaies_entre
        THEN
            monnaies_entre := monnaies_entre \/ {nb}
        END;
        
        
    /* permet de sélectionner une boisson en précisant l'étagère sur laquelle elle est installée*/
    selectDrink(et) =
        PRE
            et : etagere &
            et <= MAX_ETAGERE &
            dispo = {oui}
            
        THEN
            etagere := etagere - {et}
        END;
        
    /* permet à l'agent d'entretien de vider l'argent de la caisse et de connaître la somme d'argent récupérée*/
    money <-- takeMoney =
        BEGIN
            money := dom(caisse) ||
            caisse := {}            
        END;
        
    /*  permet au distributeur de rendre la monnaie suite à l'appui du bouton d'annulation, et de connaître la somme d'argent rendu*/
    money <-- returnMoney =
        BEGIN
            money := dom(monnaies_entre) ||
            monnaies_entre := {}            
        END
END

-- Prove2me | Theorems.Thm_Falmagne_Examples_regularCounterexampleQ_regular
-- name    : Falmagne.Examples.regularCounterexampleQ_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:22.464693+00:00
-- url     : https://prove2.me/theorems/6fc0e53d-cb5f-5b68-938e-8cdab2bb61f4
-- title:
--   Examples: regular Counterexample Q regular
-- statement:
--   The Examples construction uses the regular Counterexample Q regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L33-L36
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L33-L36

module
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Definitions.Def_EconomicsNextProof_Examples
set_option autoImplicit true
@[expose] public section
public section
open Falmagne Falmagne.Examples
open Finset EconomicsNextProof
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem Falmagne.Examples.regularCounterexampleQ_regular :
    ∀ A B : Finset (Fin 4), A ⊆ B →
      ∀ x ∈ A, regularCounterexampleQ B x ≤ regularCounterexampleQ A x := by sorry

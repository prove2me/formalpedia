-- Prove2me | Theorems.Thm_Falmagne_Examples_regularCounterexampleQ_bm
-- name    : Falmagne.Examples.regularCounterexampleQ_bm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:33.461266+00:00
-- url     : https://prove2.me/theorems/68d2877d-ba33-5486-8600-4488dfc782f8
-- title:
--   Examples: regular Counterexample Q bm
-- statement:
--   The Examples construction uses the regular Counterexample Q bm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L60-L63
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L60-L63

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

theorem Falmagne.Examples.regularCounterexampleQ_bm :
    (∑ B ∈ univ.filter (fun B : Finset (Fin 4) => {(0 : Fin 4)} ⊆ B),
      (-1 : ℚ) ^ (B \ {(0 : Fin 4)}).card * regularCounterexampleQ B 0) = -1 / 2 := by sorry

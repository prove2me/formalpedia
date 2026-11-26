-- Prove2me | Theorems.Thm_Falmagne_Examples_regularCounterexampleQ_normalized
-- name    : Falmagne.Examples.regularCounterexampleQ_normalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:28.137843+00:00
-- url     : https://prove2.me/theorems/df352b16-3033-40a0-a52c-c7f147285817
-- title:
--   Examples: regular Counterexample Q normalized
-- statement:
--   The Examples construction uses the regular Counterexample Q normalized property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L25-L29
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L25-L29

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

theorem Falmagne.Examples.regularCounterexampleQ_normalized :
    (∀ A x, 0 ≤ regularCounterexampleQ A x) ∧
    (∀ A x, x ∉ A → regularCounterexampleQ A x = 0) ∧
    (∀ A, A.Nonempty → ∑ x ∈ A, regularCounterexampleQ A x = 1) := by sorry

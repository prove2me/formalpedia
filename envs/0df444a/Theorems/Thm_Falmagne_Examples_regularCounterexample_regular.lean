-- Prove2me | Theorems.Thm_Falmagne_Examples_regularCounterexample_regular
-- name    : Falmagne.Examples.regularCounterexample_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:28:43.196835+00:00
-- url     : https://prove2.me/theorems/7e11747d-22ef-49df-ad91-395682f9601d
-- title:
--   Examples: regular Counterexample regular
-- statement:
--   The Examples construction uses the regular Counterexample regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L51-L56
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L51-L56

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

theorem Falmagne.Examples.regularCounterexample_regular :
    ∀ A B : Finset (Fin 4), A ⊆ B →
      ∀ x ∈ A, regularCounterexample B x ≤ regularCounterexample A x := by sorry

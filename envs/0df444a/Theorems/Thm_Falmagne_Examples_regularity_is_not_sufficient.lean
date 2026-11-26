-- Prove2me | Theorems.Thm_Falmagne_Examples_regularity_is_not_sufficient
-- name    : Falmagne.Examples.regularity_is_not_sufficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:30:49.355507+00:00
-- url     : https://prove2.me/theorems/a20a8b74-1ec9-5930-a5e3-9e83e6c1976f
-- title:
--   Examples: regularity is not sufficient
-- statement:
--   The Examples construction uses the regularity is not sufficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L200-L206
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Examples.lean#L200-L206

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

theorem Falmagne.Examples.regularity_is_not_sufficient :
    IsChoiceRule regularCounterexample ∧
    (∀ A B : Finset (Fin 4), A ⊆ B → ∀ x ∈ A,
      regularCounterexample B x ≤ regularCounterexample A x) ∧
    ¬ RandomUtilityRepresentable regularCounterexample := by sorry

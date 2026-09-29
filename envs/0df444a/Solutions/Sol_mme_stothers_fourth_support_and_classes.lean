-- Prove2me | solution 1 for mme_stothers_fourth_support_and_classes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T19:03:56.116741+00:00
-- url     : https://prove2.me/submissions/eeb364e3-c551-4836-ae6c-2573acd5b87e

import Theorems.Thm_mme_stothers_fourth_block_support_exact
import Theorems.Thm_mme_stothers_fourth_table1_classification

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

/-- Verifier-ready two-child reduction for milestone M1. -/
theorem solution
    {K : Type u} [Field K] :
    (∀ sigma : Fin 3 → Fin 9,
      (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockTensor sigma = 0 ↔
        (∑ s, (sigma s).val) ≠ 8) ∧
    Fintype.card
        {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8} = 45 ∧
    (∀ sigma : {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8},
      ∃! r : Fin 10,
        MME.StothersFourth.sameOrbit sigma.1
          (MME.StothersFourth.classRep r)) ∧
    (∀ r : Fin 10,
      Fintype.card
          {sigma : {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8} //
            MME.StothersFourth.sameOrbit sigma.1
              (MME.StothersFourth.classRep r)} =
        3 * MME.StothersFourth.classMultiplicity r) := by
  exact ⟨
    mme_stothers_fourth_block_support_exact,
    mme_stothers_fourth_table1_classification⟩

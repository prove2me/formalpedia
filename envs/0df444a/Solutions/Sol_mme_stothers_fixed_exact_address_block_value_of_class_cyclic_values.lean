-- Prove2me | solution 1 for mme_stothers_fixed_exact_address_block_value_of_class_cyclic_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:10:26.493952+00:00
-- url     : https://prove2.me/submissions/369cef5c-a612-45ae-8057-fe2cafed141e

import Theorems.Thm_mme_stothers_fixed_address_group_by_ordered_grade_types
import Theorems.Thm_mme_stothers_fixed_ordered_grade_product_value_of_class_cyclic_values
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ)
    (hclass : ∀ (r : Fin 10) (V : ℝ),
      0 ≤ V → V < MME.StothersFourth.classValue 6 tau r →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6
            (MME.StothersFourth.classRep r 0)
            (MME.StothersFourth.classRep r 1)
            (MME.StothersFourth.classRep r 2))) tau V) :
    ∀ (m : ℕ) (a : MME.StothersFourth.FixedExactOuterAddress m)
        (W : ℝ),
      0 ≤ W →
      W < (∏ r : Fin 10,
        (MME.StothersFourth.classValue 6 tau r) ^
          (MME.StothersFourth.classMultiplicity r *
            MME.StothersFourth.fixedProfileCount m r)) →
      HasTauValueAtLeast
        (gradedAddressBlock
          (MME.StothersFourth.cwFourthCanonicalGrading K 6) a.1)
        tau W := by
  intro m a W hW hstrict
  have hgroup :=
    mme_stothers_fixed_address_group_by_ordered_grade_types
      (K := K) m a
  have hvalue :=
    mme_stothers_fixed_ordered_grade_product_value_of_class_cyclic_values
      (K := K) tau hclass m W hW hstrict
  exact mme_HasTauValueAtLeast_mono_restrict hgroup.2 hvalue

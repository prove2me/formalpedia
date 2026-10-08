-- Prove2me | solution 1 for measurable_prefixRevenueRebuild
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:43:41.369215+00:00
-- url     : https://prove2.me/submissions/846b87e4-b449-4e51-b45e-d5d8c59da7a9

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_abs_bound
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_extensional_on_prefix
import Definitions.Def_prefixRevenueRebuild

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution (k : ℕ) :
    Measurable (prefixRevenueRebuild k) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j ∈ Finset.Icc 1 k
  · simp only [prefixRevenueRebuild, dif_pos hj]
    exact (measurable_pi_apply (X := fun _ : Finset.Icc 1 k => ℝ)
      (⟨j, hj⟩ : Finset.Icc 1 k)).comp
      (show Measurable (fun z : ℝ × (Finset.Icc 1 k → ℝ) => z.2) from
        measurable_snd)
  · by_cases hnext : j = k + 1
    · simpa [prefixRevenueRebuild, hj, hnext] using measurable_fst
    · simpa [prefixRevenueRebuild, hj, hnext] using
        (measurable_const : Measurable fun _ : ℝ × (Finset.Icc 1 k → ℝ) => (0 : ℝ))

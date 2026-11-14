-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_indep_comap_ae_equal_measurable_source_20261113
-- name    : AvramDividend.Classical.avram_a24_indep_comap_ae_equal_measurable_source_20261113
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T00:00:37.167205+00:00
-- url     : https://prove2.me/theorems/d4e0e6c1-3b0b-4c10-92b3-72a8655f83bc
-- title:
--   Independence of measurable random variable from source sigma-algebra is invariant under almost-everywhere equality
-- statement:
--   On an original probability space, two globally measurable random variables agreeing almost everywhere have identical independence relationships with every sub-sigma-algebra of the original measurable space; no filtration completion is needed.
-- source:
--   Pinned Mathlib indep_iff_forall_indepSet, measurableSet_comap, MeasureTheory.measure_congr, and indepSet_iff_measure_inter_eq_mul.

import Mathlib
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- AE-equal measurable random variables generate the same independence relationships with a source sub-sigma-algebra. -/

theorem AvramDividend.Classical.avram_a24_indep_comap_ae_equal_measurable_source_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (A : MeasurableSpace Ω) (hA : A ≤ mΩ)
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hEq : f =ᵐ[P] g)
    (hInd : Indep (MeasurableSpace.comap f inferInstance) A P) :
    Indep (MeasurableSpace.comap g inferInstance) A P := by sorry

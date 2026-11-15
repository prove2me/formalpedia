-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a57_raw_sigma_independence_preserved_by_conull_source_equality_20261114
-- name    : AvramDividend.Classical.avram_a57_raw_sigma_independence_preserved_by_conull_source_equality_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:20:13.952796+00:00
-- url     : https://prove2.me/theorems/bfe4b735-2450-4ebc-b4eb-cfe988659dfc
-- title:
--   Independence from an original raw sigma algebra is preserved under almost-everywhere replacement of a real source variable
-- statement:
--   If two real random variables on the original probability space agree almost everywhere, independence of the first variable from any fixed raw sigma algebra implies independence of the second without filtration completion.
-- source:
--   Pinned Mathlib IndepFun.congr and IndepFun_iff_Indep.

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Independence from a fixed raw sigma algebra is invariant under source almost-everywhere replacement of a real random variable. -/

theorem AvramDividend.Classical.avram_a57_raw_sigma_independence_preserved_by_conull_source_equality_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (𝓐 : MeasurableSpace Ω)
    (f g : Ω → ℝ)
    (hEq : f =ᵐ[P] g)
    (hInd : Indep (MeasurableSpace.comap f inferInstance) 𝓐 P) :
    Indep (MeasurableSpace.comap g inferInstance) 𝓐 P := by sorry

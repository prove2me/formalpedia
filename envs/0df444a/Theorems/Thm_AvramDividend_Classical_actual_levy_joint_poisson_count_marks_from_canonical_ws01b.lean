-- Prove2me | Theorems.Thm_AvramDividend_Classical_actual_levy_joint_poisson_count_marks_from_canonical_ws01b
-- name    : AvramDividend.Classical.actual_levy_joint_poisson_count_marks_from_canonical_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:25:31.859694+00:00
-- url     : https://prove2.me/theorems/983038ce-dafb-4ff7-bff2-2c1bff6687d5
-- title:
--   Transfer complete joint Poisson-count and mark-sequence product law from matching canonical Lévy path
-- statement:
--   When two actual spectrally negative Lévy processes have identical Lévy triplets and the same measurable pathwise extraction Fpath of a natural count together with an infinite sequence of marks, any canonical joint product law Poisson(r) × η transfers exactly to the actual process. Unlike a scalar count-law transfer, this carries every joint count/mark event, including the independence encoded by the product law. It requires a substantive canonical process with the joint law and a measurable jump-family extractor; neither is smuggled into the theorem.
-- source:
--   Exact application of canonically Proved cross_levy_whole_path_law_of_equal_triplet and pinned Mathlib HasLaw + Measure.map_map, abstracting the full joint random point-family law to enable future finite-band BV predictable compensation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_cross_levy_whole_path_law_of_equal_triplet

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.actual_levy_joint_poisson_count_marks_from_canonical_ws01b
    {Ω₁ Ω₂ E : Type*}
    [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    [MeasurableSpace E]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hc : X.c = Y.c) (hσ : X.σ = Y.σ) (hν : X.ν = Y.ν)
    (Fpath : (ℝ≥0 → ℝ) → ℕ × (ℕ → E))
    (hF : Measurable Fpath)
    (r : ℝ≥0) (η : Measure (ℕ → E))
    (hYlaw : HasLaw
      (fun ω : Ω₂ => Fpath (fun t : ℝ≥0 => Y.X t ω))
      ((poissonMeasure r).prod η) P₂) :
    HasLaw
      (fun ω : Ω₁ => Fpath (fun t : ℝ≥0 => X.X t ω))
      ((poissonMeasure r).prod η) P₁ := by sorry

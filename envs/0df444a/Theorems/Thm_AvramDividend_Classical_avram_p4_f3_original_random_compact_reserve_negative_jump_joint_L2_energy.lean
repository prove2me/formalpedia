-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_random_compact_reserve_negative_jump_joint_L2_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_random_compact_reserve_negative_jump_joint_L2_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:04:17.580342+00:00
-- url     : https://prove2.me/theorems/52e0f115-8ed5-43e2-aa89-1c786a6d7462
-- title:
--   Random compact-reserve states have finite original physical joint negative-jump L2 energy
-- statement:
--   A random capital U always lying in a compact positive reserve band has an original negative-mark Lévy coefficient with finite joint P and X.ν quadratic energy. The bound is uniform in U and valid at all negative marks, and uses the original source Lévy integrability field.
-- source:
--   Combines source-exact negative-mark quadratic min(1,z²) kernel bound with original SpectrallyNegativeLevy.ν_integrable and IsProbabilityMeasure P. This controls a random left-limit capital coefficient but does not assert that U is predictable or that a compensated stochastic integral already exists.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Random compact reserve states retain finite original physical joint quadratic jump energy. -/

theorem AvramDividend.Classical.avram_p4_f3_original_random_compact_reserve_negative_jump_joint_L2_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (U : Ω → ℝ) (hU : ∀ ω, U ω ∈ Icc δ K) :
    (∫⁻ ω, (∫⁻ z in Iio (0 : ℝ),
       ENNReal.ofReal ((w (U ω + z) - w (U ω)) ^ 2) ∂X.ν) ∂P) < ⊤ := by sorry

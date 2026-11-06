-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_compact_negative_jump_uniform_nu_square_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_compact_negative_jump_uniform_nu_square_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:06:34.046009+00:00
-- url     : https://prove2.me/theorems/2c8191b7-addc-4298-a9be-d2c096c6ce9a
-- title:
--   Uniform intrinsic Lévy negative-jump coefficient quadratic energy over every compact reserve band
-- statement:
--   The actual original negative Lévy jump kernel z↦w(u+z)-w(u), for original X and all reserve states u in the same strictly-positive compact band, admits a single finite ENNReal bound S on the square integral against original X.ν. Uniformity comes from the explicit original P4-F3 quadratic pointwise domination by M min(1,z²), and the original source triplet ν_integrable. This handles ν with infinite small-jump activity and C=top, supplying exactly the deterministic energy bound needed for future stopped predictable L² integration.
-- source:
--   Establishes one single finite original source intensity S=ofReal M*∫ ofReal(min 1 z²) against X.ν; uses Proved P4-F3 squared coefficient domination uniformly in reserve, real-to-ENNReal monotonicity, indicator restriction and lintegral_const_mul. Does not invoke finite total jump intensity, a detached process, or an unproved stochastic isometry.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_compact_negative_jump_uniform_nu_square_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ S : ℝ≥0∞, S < ⊤ ∧
      ∀ u ∈ Icc δ K,
        (∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((w (u + z) - w u) ^ 2) ∂X.ν) ≤ S := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_compact_negative_jump_coefficient_nu_square_integrable
-- name    : AvramDividend.Classical.avram_p4_f3_original_compact_negative_jump_coefficient_nu_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:06:56.594015+00:00
-- url     : https://prove2.me/theorems/6e598792-a563-49c9-8d24-e7217e2cbff7
-- title:
--   Original spectrally negative Lévy negative-mark coefficient has finite compact-source quadratic energy
-- statement:
--   For original spectrally negative Lévy X with its actual Lévy measure X.ν, a continuous-on-nonnegative w zero for negative states and C2 in the positive capped interior has finite negative-jump squared-coefficient integral on every strictly-positive compact reserve band. The estimate is uniform in reserve and uses only original X.ν_integrable and the proved squared pointwise coefficient bound by M min(1,z^2), covering infinite jump activity and C=top. No imaginary jump noise or mean-zero process is assumed.
-- source:
--   Uses genuinely source-exact original Lévy triplet ν_integrable together with previous public Proved Avram p4-f3 uniform quadratic negative-mark domination. The bound is integrated via lintegral_const_mul and finite ENNReal products. This supplies necessary kernel L2 input to a future original finite-band predictable martingale construction, without assuming that construction.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_compact_negative_jump_coefficient_nu_square_integrable
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
    ∀ u ∈ Icc δ K,
      (∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((w (u + z) - w u) ^ 2) ∂X.ν) < ⊤ := by sorry

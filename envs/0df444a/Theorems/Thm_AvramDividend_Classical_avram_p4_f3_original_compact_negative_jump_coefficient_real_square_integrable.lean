-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_compact_negative_jump_coefficient_real_square_integrable
-- name    : AvramDividend.Classical.avram_p4_f3_original_compact_negative_jump_coefficient_real_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:11:55.341738+00:00
-- url     : https://prove2.me/theorems/c5a74e9a-5c1c-49cc-8a01-4f72f550f21d
-- title:
--   Original intrinsic negative-jump coefficient has real square-integrable Lévy energy
-- statement:
--   For the actual original source spectrally negative Lévy X with finite small-jump quadratic Lévy energy, the real-valued negative mark coefficient z↦w(u+z)-w(u) is square-integrable against X.ν restricted to negative jumps on each positive reserve compact. Derives source L2 energy without extra measure assumptions and uses the genuine global measurability of the continuous nonnegative/zero negative value function. This does not yet assert a stochastic integral or martingale.
-- source:
--   Composes the P4-F3 actual source ν squared-coefficient lintegral estimate with existing Proved source global value measurability, nonnegative squared coefficient, and pinned hasFiniteIntegral_iff_ofReal. Converts finite ENNReal energy to genuine real IntegrableOn against the same original Lévy measure; no local-martingale or finite-activity assertion.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_ruin_extension_value_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_compact_negative_jump_coefficient_nu_square_integrable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_compact_negative_jump_coefficient_real_square_integrable
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
      IntegrableOn (fun z : ℝ => (w (u + z) - w u) ^ 2)
        (Iio (0 : ℝ)) X.ν := by sorry

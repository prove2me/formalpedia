-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
-- name    : AvramDividend.Classical.avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:17:56.002132+00:00
-- url     : https://prove2.me/theorems/b47238ec-d8b3-45ab-858e-b3a9a9ed53c4
-- title:
--   Original finite-activity negative marked jump count is almost surely finite at any deterministic horizon
-- statement:
--   For an original spectrally negative Levy process with finite negative-jump Levy intensity, the literal count of all negative source jumps up to any fixed finite time is finite almost surely. Combine the original arbitrary Borel marked unconditional Levy rate with finite intensity, and use original filtration measurability of the marked nonnegative integral plus ae_lt_top. No bounded-variation assumption, extra probability space, or finite cutoff is allowed. Enables almost-sure finite signed jump accounting for original finite-activity mixed Gaussian residual increments and stopped Ito-Meyer source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_general_mark_lintegral_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_borel_marked_unconditional_levy_rate
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) ≠ ⊤ := by sorry

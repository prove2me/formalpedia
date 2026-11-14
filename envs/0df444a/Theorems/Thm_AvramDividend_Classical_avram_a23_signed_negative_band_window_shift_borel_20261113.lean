-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_signed_negative_band_window_shift_borel_20261113
-- name    : AvramDividend.Classical.avram_a23_signed_negative_band_window_shift_borel_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:10:54.652219+00:00
-- url     : https://prove2.me/theorems/330a4c16-4353-4be1-abba-89681d06d6b6
-- title:
--   True original signed negative marked window is a Borel future-increment path statistic
-- statement:
--   The physical signed negative retained-mark jump integral on (s,t] is exactly a measurable function of the original shifted future-increment path, for every sample path of a spectrally negative Levy process.
-- source:
--   Proved generic cadlag mark weight lintegral Borel theorem b50e56f2; exact original signed shift theorem 238b5785; no auxiliary probability space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_negative_band_shift_integral_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_generic_negative_mark_window_integral_formula
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true original signed retained-band window is a measurable future-path statistic. -/

theorem AvramDividend.Classical.avram_a23_signed_negative_band_window_shift_borel_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ J : (ℝ≥0 → ℝ) → ℝ, Measurable J ∧
      ∀ ω : Ω,
        let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
        let μ : Measure (ℝ≥0 × ℝ) :=
          (Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
        (∫ p in (Ioc s t ×ˢ B), p.2 ∂μ) =
          J (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by sorry

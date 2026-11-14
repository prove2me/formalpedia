-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_uniform_signed_negative_band_window_borel_20261113
-- name    : AvramDividend.Classical.avram_a23_uniform_signed_negative_band_window_borel_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:23:19.434591+00:00
-- url     : https://prove2.me/theorems/99b6757c-288d-4fca-9d9d-1e4c92f6ca30
-- title:
--   One measurable physical signed negative-jump window functional works at all original deterministic starts
-- statement:
--   For a fixed compensated negative mark band and time duration, the actual original signed marked jump integral over every translated window is the same measurable functional of its shifted original Levy future-increment path, for all starts and all sample paths.
-- source:
--   Proved cadlag marked lintegral Borel theorem b50e56f2, original signed physical shift 238b5785, original shifted path cadlag.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_negative_band_shift_integral_exact
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_generic_negative_mark_window_integral_formula
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A single Borel future-path functional works for every original starting time at fixed horizon. -/

theorem AvramDividend.Classical.avram_a23_uniform_signed_negative_band_window_borel_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (T : ℝ≥0) :
    ∃ J : (ℝ≥0 → ℝ) → ℝ, Measurable J ∧
      ∀ (s : ℝ≥0) (ω : Ω),
        let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
        let μ : Measure (ℝ≥0 × ℝ) :=
          (Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
        (∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂μ) =
          J (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by sorry

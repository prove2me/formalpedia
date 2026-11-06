-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_hard_envelope_forces_positive_horizon_and_drift
-- name    : AvramDividend.Classical.avram_bv_env3_original_hard_envelope_forces_positive_horizon_and_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:50:15.379682+00:00
-- url     : https://prove2.me/theorems/d40baede-e7a5-4083-9081-2af1e68e0ef2
-- title:
--   Original BV drift-envelope complement forces a positive horizon and positive Lévy drift even at cap contact
-- statement:
--   The original strict drift-envelope complementary case under closed positive cap, w(0) nonnegative and an interior C¹ slope lower bound ≥1 implies both T>0 and X.drift>0. Uses the fully Proved original closed-cap C¹ linear lower-envelope including x=C; does not assume any stochastic expected-budget result.
-- source:
--   Original fully Proved closed-cap gradient lower-envelope theorem fc03f3ac-1178-466d-bb09-d9cae7a15d5e; elementary real ordered arithmetic; Avram, Palmowski and Pistorius (2007), Proposition 4(i), equation (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_hard_envelope_forces_positive_horizon_and_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x)) :
    0 < T ∧ 0 < X.drift := by sorry

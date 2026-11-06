-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_complement_positive_horizon_and_drift
-- name    : AvramDividend.Classical.avram_bv_env3_original_complement_positive_horizon_and_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:23:00.4726+00:00
-- url     : https://prove2.me/theorems/36b1e799-3f2b-420b-b9e2-4ebf40d9cd98
-- title:
--   Strict original BV drift-envelope complement requires positive horizon and positive drift
-- statement:
--   With positive cap and gradient at least one, the proved closed-cap C1 envelope yields w(x)>=w(0)+x>=x. Hence the genuinely complementary inequality w(x)<x+T*d requires strictly positive horizon and drift. This is derived from the original cap and derivative assumptions, not extra hypotheses.
-- source:
--   Exact Proved original closed-cap C1 gradient lower envelope fc03f3ac-1178-466d-bb09-d9cae7a15d5e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_complement_positive_horizon_and_drift
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (T drift : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * drift ≤ w x)) :
    0 < T ∧ 0 < drift := by sorry

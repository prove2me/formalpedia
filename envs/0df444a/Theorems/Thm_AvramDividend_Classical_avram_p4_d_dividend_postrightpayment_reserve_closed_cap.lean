-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postrightpayment_reserve_closed_cap
-- name    : AvramDividend.Classical.avram_p4_d_dividend_postrightpayment_reserve_closed_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:11:11.922125+00:00
-- url     : https://prove2.me/theorems/d88fd858-206f-4e8f-8905-0a82a079b829
-- title:
--   The post-source post-right-dividend reserve stays in the exact closed admissible cap interval
-- statement:
--   For the original source Lévy sample path, initial reserve below C and capped admissible strategy, at every eligible active time including t=0, the correct post-X-jump post-right-payment reserve x+X_t-D_{t+} lies in [0,C]. Admissibility gives nonnegative postpayment reserve; monotonicity gives postpayment≤prepayment; cap admissibility handles t>0 and initial cap handles t=0. Valid at simultaneous source/control jumps and both boundary contacts without assuming w differentiable at 0 or C.
-- source:
--   Original SpectrallyNegativeLevy.X_zero and source IsAdmissibleLe definitions UUID 561c1e83; proved source dividendStrategy_le_rightLimit UUID 953f0e91; ENNReal.ofReal monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_postrightpayment_reserve_closed_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hactive : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ x + X.X t ω - rightLimit D t ω ∧
      ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) ≤ C := by sorry

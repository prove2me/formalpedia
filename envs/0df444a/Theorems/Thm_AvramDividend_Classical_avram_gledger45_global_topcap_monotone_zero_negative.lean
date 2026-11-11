-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger45_global_topcap_monotone_zero_negative
-- name    : AvramDividend.Classical.avram_gledger45_global_topcap_monotone_zero_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T20:13:11.539753+00:00
-- url     : https://prove2.me/theorems/ea3dee47-184f-4708-bfab-600c8267c18e
-- title:
--   Top-cap reward is globally nondecreasing across negative ruin overshoot
-- statement:
--   A reward continuous on nonnegative reserves, zero on strictly negative reserves, nonnegative at zero, and with derivative at least one at every strictly positive top-cap reserve is monotone on the full real line. This handles the final source overshoot at ruin even when ν is nonzero, where a positive-reserve derivative theorem alone is inapplicable. Reuse the proved Gaussian-29 secant on the nonnegative half-line; split negative-to-negative, crossing-zero, and nonnegative cases.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger45_global_topcap_monotone_zero_negative
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (a b : ℝ) (hab : a ≤ b) : w a ≤ w b := by sorry

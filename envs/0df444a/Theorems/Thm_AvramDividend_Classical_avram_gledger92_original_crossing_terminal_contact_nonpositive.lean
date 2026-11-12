-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger92_original_crossing_terminal_contact_nonpositive
-- name    : AvramDividend.Classical.avram_gledger92_original_crossing_terminal_contact_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:18:11.653341+00:00
-- url     : https://prove2.me/theorems/368044e9-7371-479f-9cc2-e1edeaa18547
-- title:
--   Original postpayment terminal value cannot exceed the pre-dividend crossing value
-- statement:
--   For the original dividend strategy on the same sample, the right-limit dividend total is nondecreasing. The globally nondecreasing top-cap reward therefore makes the postpayment reward at a crossing endpoint no greater than the reward with the dividend level frozen at the cell start, even at ruin where the reserve may be negative.
-- source:
--   Strictly smaller terminal sign fact for gledger81 16e988d7. Handles the final crossing cell without requiring the postpayment reserve to remain nonnegative at ruin.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_gledger45_global_topcap_monotone_zero_negative
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger92_original_crossing_terminal_contact_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (ω : Ω)
    (a b : ℝ≥0) (hab : a ≤ b)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    w (x + X.X b ω - rightLimit D b ω) ≤
      w (x + X.X b ω - rightLimit D a ω) := by sorry

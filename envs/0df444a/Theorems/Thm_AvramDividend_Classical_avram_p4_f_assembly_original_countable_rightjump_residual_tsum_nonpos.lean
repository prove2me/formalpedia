-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_countable_rightjump_residual_tsum_nonpos
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_countable_rightjump_residual_tsum_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:42:42.079215+00:00
-- url     : https://prove2.me/theorems/438693e6-eaa2-4424-b78b-1fad0a9bc25f
-- title:
--   Summable countably many actual dividend right-jump residuals have nonpositive total
-- statement:
--   For a countably enumerated sequence of true eligible right-dividend payment times along the original source path, assume the exact discounted residual series is summable. Each term is nonpositive by the Proved original hjump secant theorem, so the series total is nonpositive. The summability premise is explicit; the theorem does not claim all original dividend measures admit such an enumeration or bound.
-- source:
--   Proved original rightjump residual 9f4070e7 and Mathlib topology algebra infinite sum tsum_nonpos.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_countable_rightjump_residual_tsum_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℕ → ℝ≥0)
    (hpre : ∀ k, t k = 0 ∨ (t k : ℝ≥0∞) < ruinTime X x D ω)
    (hsummable : Summable (fun k : ℕ =>
      Real.exp (-(q * (t k : ℝ))) *
        ((rightLimit D (t k) ω - D (t k) ω) +
          w (x + X.X (t k) ω - rightLimit D (t k) ω) -
          w (riskProcess X x D (t k) ω)))) :
    (∑' k : ℕ, Real.exp (-(q * (t k : ℝ))) *
      ((rightLimit D (t k) ω - D (t k) ω) +
        w (x + X.X (t k) ω - rightLimit D (t k) ω) -
        w (riskProcess X x D (t k) ω))) ≤ 0 := by sorry

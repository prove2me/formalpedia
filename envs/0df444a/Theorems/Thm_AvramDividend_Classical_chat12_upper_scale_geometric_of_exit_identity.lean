-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_upper_scale_geometric_of_exit_identity
-- name    : AvramDividend.Classical.chat12_upper_scale_geometric_of_exit_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:22:29.759167+00:00
-- url     : https://prove2.me/theorems/b6357137-20f9-48c9-8907-b343e7b7b494
-- title:
--   Conditional scale-ratio geometric upper bound for killed dividend records
-- statement:
--   Assuming the strict discounted two-sided-exit expectation is identified with the q-scale-function ratio W(a)/W(a+epsilon), every killed n-th record expected reward is bounded above by epsilon times the n-th power of that ratio in ENNReal. The proof uses the Proved conditional upper geometric expectation theorem and positivity of the scale-function ratio. The exit ratio equality is deliberately an explicit premise, so no still-Open two-sided-exit theorem is imported.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat12_killed_firstRecord_grid_upper_of_trueExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_upper_scale_geometric_of_exit_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε)
    (hWright : 0 < W (a + ε)) (hWa : 0 ≤ W a)
    (hWinc : W a < W (a + ε))
    (hExit : (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
    else 0 ∂P) = ENNReal.ofReal (W a / W (a + ε))) :
    ∀ n : ℕ,
      (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P) ≤
        ENNReal.ofReal (ε * (W a / W (a + ε)) ^ n) := by sorry

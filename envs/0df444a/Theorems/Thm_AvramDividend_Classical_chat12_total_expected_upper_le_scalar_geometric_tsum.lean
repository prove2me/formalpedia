-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_le_scalar_geometric_tsum
-- name    : AvramDividend.Classical.chat12_total_expected_upper_le_scalar_geometric_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:27:18.15708+00:00
-- url     : https://prove2.me/theorems/6c023804-2aa2-44ba-938b-71ebd5fd52a6
-- title:
--   Total expected killed-record dividends bounded by a scalar geometric series
-- statement:
--   Under an explicit identification of the true discounted strict two-sided-exit factor with ENNReal.ofReal p (p≥0), the sum across all levels of discounted expected killed-record payments is bounded by the scalar extended-real geometric series Σ ENNReal.ofReal (epsilon*p^n). This follows by summing the fully Proved conditional upper geometric record bound; it is independent of the still-Open q-scale exit ratio and of Chat 5's pathwise dividend-measure budget.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_chat12_killed_firstRecord_grid_upper_of_trueExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_total_expected_upper_le_scalar_geometric_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (p : ℝ) (hp : 0 ≤ p)
    (hExit : (∫⁻ ω, if
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal p) :
    (∑' n : ℕ, (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) ≤
      (∑' n : ℕ, ENNReal.ofReal (ε * p ^ n)) := by sorry

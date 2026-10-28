-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_killed_firstRecord_grid_upper_of_trueExit
-- name    : AvramDividend.Classical.chat12_killed_firstRecord_grid_upper_of_trueExit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:45:40.312077+00:00
-- url     : https://prove2.me/theorems/128b4dcb-72e4-4717-81fb-f4bf979171ea
-- title:
--   Conditional strict-exit geometric upper killed-record budgets
-- statement:
--   Under the explicit identity that the true discounted strict ε-up-before-(-a)-down exit expectation equals ENNReal.ofReal p, with p≥0, the discounted expected killed n-th record reward is at most ENNReal.ofReal (ε*p^n). This invokes the Proved strong-Markov upper one-cycle reward and Proved geometric upper iteration including the initial ε envelope. It does not assume any q-scale function or any Open corrected two-sided-exit identity.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.GCongr
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_next_expected_le_current_mul_twoSided
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_geometric_expected_upper_of_step

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_killed_firstRecord_grid_upper_of_trueExit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (a ε : ℝ) (ha : 0 < a)
    (hε : 0 < ε) (p : ℝ) (hp : 0 ≤ p)
    (hExit : (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
    else 0 ∂P) = ENNReal.ofReal p) :
    ∀ n : ℕ, (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
        barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp
        (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
    else 0 ∂P) ≤ ENNReal.ofReal (ε * p ^ n) := by sorry

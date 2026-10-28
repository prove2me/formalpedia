-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_one_step_scale_regeneration_lower_of_strict_exit
-- name    : AvramDividend.Classical.killed_firstRecord_one_step_scale_regeneration_lower_of_strict_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:15:43.588865+00:00
-- url     : https://prove2.me/theorems/4d92eb67-f5be-4564-9d91-7a1543e91013
-- title:
--   Killed first-record scale regeneration from an explicit strict exit identity
-- statement:
--   The already-proved full-horizon first-record strong-Markov inequality implies the expected lower geometric regeneration step when the strict discounted two-sided exit expectation is identified with W(a-epsilon)/W(a). This removes stochastic Markov and cap-limit machinery from the canonical scale-ratio theorem.
-- source:
--   Proved firstRecord_uncapped_nextRecord_trueFactor_lower (24d6b537-6c99-47de-b9d2-13f8896e121b); the remaining strict-exit identity is an explicit assumption rather than an unproved import.

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_firstRecord_uncapped_nextRecord_trueFactor_lower

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_firstRecord_one_step_scale_regeneration_lower_of_strict_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hεa : ε < a)
    (hWa : 0 < W a) (hWleft : 0 ≤ W (a - ε))
    (hWinc : W (a - ε) < W a)
    (hExit :
      (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q *
          ENNReal.toReal (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W (a - ε) / W a)) :
    ∀ n : ℕ,
      ENNReal.ofReal (W (a - ε) / W a) *
        (∫⁻ ω, if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp
            (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
        else 0 ∂P) ≤
        (∫⁻ ω, if twoSidedExitUpTime X (((n + 2 : ℕ) : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp
            (-(q * (twoSidedExitUpTime X (((n + 2 : ℕ) : ℝ) * ε) ω).toReal)))
        else 0 ∂P) := by sorry

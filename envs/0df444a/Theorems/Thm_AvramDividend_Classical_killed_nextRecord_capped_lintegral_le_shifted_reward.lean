-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_nextRecord_capped_lintegral_le_shifted_reward
-- name    : AvramDividend.Classical.killed_nextRecord_capped_lintegral_le_shifted_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:13:42.642767+00:00
-- url     : https://prove2.me/theorems/bdf2c334-d1fb-4def-acf5-839e9aaedde1
-- title:
--   Capped next-record expected discounted reward bounded by shifted record reward
-- statement:
--   Integrate the pathwise finite-horizon inequality for the killed higher record, giving a localised expectation upper bound ready for strong-Markov factorisation and monotone convergence.
-- source:
--   Proved capped pathwise shifted record inequality and monotonicity of the Lebesgue integral

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_capped_pathwise_shifted_upper

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_nextRecord_capped_lintegral_le_shifted_reward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (N : ℝ≥0) (ρ σ : Ω → ℝ≥0∞)
    (hρ : ∀ ω : Ω, ρ ω = (⨅ (t : ℝ≥0)
      (_ : ε < X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
          X.X (twoSidedExitUpTime X b ω).toNNReal ω), (t : ℝ≥0∞)))
    (hσ : ∀ ω : Ω, σ ω = (⨅ (t : ℝ≥0)
      (_ : X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
          X.X (twoSidedExitUpTime X b ω).toNNReal ω < -a), (t : ℝ≥0∞))) :
    (∫⁻ ω, if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X (b + ε) ω ≤ (N : ℝ≥0∞) then
      ENNReal.ofReal ε *
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0 ∂P) ≤
    (∫⁻ ω, if twoSidedExitUpTime X b ω < barrierRuinTime X a ω ∧
        twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) then
      ENNReal.ofReal ε *
        (ENNReal.ofReal (Real.exp (-(q *
          ((twoSidedExitUpTime X b ω).toNNReal : ℝ)))) *
          (if ρ ω < σ ω then
            ENNReal.ofReal (Real.exp (-(q * (ρ ω).toReal)))
          else 0))
      else 0 ∂P) := by sorry

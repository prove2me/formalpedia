-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_nextRecord_lintegral_le_shifted_twoSided_reward
-- name    : AvramDividend.Classical.killed_nextRecord_lintegral_le_shifted_twoSided_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:27:29.868977+00:00
-- url     : https://prove2.me/theorems/1827d6bd-8bd1-4314-917f-9ea6cc303dcc
-- title:
--   Expected next-record payment is bounded by the shifted two-sided killed reward
-- statement:
--   The killed first-record discount inequality transfers from each Lévy sample path to its nonnegative expected dividend value, before the final stopped Markov factorisation.
-- source:
--   Pointwise accepted global killed-record upper bound and monotonicity of the Lebesgue integral for nonnegative extended-real functions.

import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_global_shifted_twoSided_upper

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_nextRecord_lintegral_le_shifted_twoSided_reward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ρ σ : Ω → ℝ≥0∞)
    (hρ : ∀ ω : Ω,
      ρ ω = (⨅ (t : ℝ≥0)
        (_ : ε < X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
            X.X (twoSidedExitUpTime X b ω).toNNReal ω),
        (t : ℝ≥0∞)))
    (hσ : ∀ ω : Ω,
      σ ω = (⨅ (t : ℝ≥0)
        (_ : X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
            X.X (twoSidedExitUpTime X b ω).toNNReal ω < -a),
        (t : ℝ≥0∞))) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
        ENNReal.ofReal ε *
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0 ∂P) ≤
    (∫⁻ ω,
      ENNReal.ofReal ε *
        (ENNReal.ofReal (Real.exp (-(q *
          ((twoSidedExitUpTime X b ω).toNNReal : ℝ)))) *
          (if ρ ω < σ ω then
            ENNReal.ofReal (Real.exp (-(q * (ρ ω).toReal)))
          else 0)) ∂P) := by sorry

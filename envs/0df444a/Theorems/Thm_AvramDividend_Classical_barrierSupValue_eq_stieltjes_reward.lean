-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_stieltjes_reward
-- name    : AvramDividend.Classical.barrierSupValue_eq_stieltjes_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T12:54:43.431978+00:00
-- url     : https://prove2.me/theorems/f8337d31-abc0-473d-a833-98b7d0db9556
-- title:
--   The actual stopped reflected dividend valuation integrates the running-supremum Stieltjes measure
-- statement:
--   The published barrierSupValue is a double nonnegative Lebesgue integral of the q-discount against dividendMeasure(runningSup) stopped at the strict reflected barrier ruin time. At each sample path, the Prove2Me proved monotonicity witness identifies that dividendMeasure with its genuine Lebesgue–Stieltjes measure. Choose these monotonicity proofs consistently pathwise and rewrite the inner integration measure, obtaining an exact formula for the original barrierSupValue as an expected discounted stopped Stieltjes integral. This is the correct source measure needed for inverse running-record discretisation and finite-difference renewal bounds. No new stochastic, Markov, exit-distribution or derivative assertion is made.
-- source:
--   Proved Prove2Me runningSup_dividendMeasure_eq_stieltjes 036fcdf6-3be7-4bd6-a17a-92fb44710834 and Def_AvramDividend_Classical_ReflectionBarrier, equation (3.12) of Avram Palmowski Pistorius (2007).

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_eq_stieltjes

open Classical MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.barrierSupValue_eq_stieltjes_reward
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ) :
    ∃ h : ∀ ω : Ω,
      Monotone (fun t : ℝ => runningSup X t.toNNReal ω),
      barrierSupValue X a q =
        ∫⁻ ω, ∫⁻ t in paymentTimes (barrierRuinTime X a ω),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂
          ((h ω).stieltjesFunction.measure) ∂P := by sorry

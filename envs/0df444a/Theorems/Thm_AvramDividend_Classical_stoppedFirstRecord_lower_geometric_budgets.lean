-- Prove2me | Theorems.Thm_AvramDividend_Classical_stoppedFirstRecord_lower_geometric_budgets
-- name    : AvramDividend.Classical.stoppedFirstRecord_lower_geometric_budgets
-- status  : Open
-- author  : @WillR
-- created : 2026-10-25T13:40:41.599346+00:00
-- url     : https://prove2.me/theorems/f3f6e8f7-44c0-44d7-a529-64dd8774ebbf
-- title:
--   Measurable stopped first-record budgets with scale-ratio lower expectations
-- statement:
--   For a standing spectrally negative Lévy process, a positive discount rate, and a positive barrier, each sufficiently small positive record-height mesh with 0<W(a-ε)<W(a) admits a sequence of nonnegative measurable first-record discounted payments. Their countable pathwise sum is bounded by the genuine stopped Stieltjes dividend reward, and their expected values dominate ε[W(a-ε)/W(a)]^(n+1). This isolates the stochastic first-passage and strong-Markov regeneration estimate needed for the lower stopped-renewal inequality, without incorporating the analytic derivative-limit step.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, reflected-supremum first-record renewal construction; existing Proved stopped Stieltjes record-cell bounds and geometric Tonelli comparison.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.stoppedFirstRecord_lower_geometric_budgets
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ) (ha : 0 < a)
    (hε : 0 < ε) (hεa : ε < a)
    (hWa : 0 < W a) (hWleft : 0 ≤ W (a - ε))
    (hWinc : W (a - ε) < W a) :
    ∃ w : ℕ → Ω → ℝ≥0∞,
      (∀ n : ℕ, AEMeasurable (w n) P) ∧
      (∀ᵐ ω ∂P, (∑' n, w n ω) ≤
        (∫⁻ t, if t ∈ paymentTimes (barrierRuinTime X a ω)
          then ENNReal.ofReal (Real.exp (-(q * t))) else 0
          ∂(dividendMeasure (runningSup X) ω))) ∧
      (∀ n : ℕ,
        ENNReal.ofReal (ε * (W (a - ε) / W a) ^ (n + 1)) ≤
          (∫⁻ ω, w n ω ∂P)) := by sorry

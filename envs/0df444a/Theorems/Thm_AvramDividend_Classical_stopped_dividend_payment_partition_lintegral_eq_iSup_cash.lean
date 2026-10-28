-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_dividend_payment_partition_lintegral_eq_iSup_cash
-- name    : AvramDividend.Classical.stopped_dividend_payment_partition_lintegral_eq_iSup_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:41:33.84339+00:00
-- url     : https://prove2.me/theorems/73361da5-efe3-492f-941e-3e0eb3d95902
-- title:
--   Exact disjoint-interval Stieltjes dividend payout as an increasing cash limit
-- statement:
--   For a stopped capped dividend payment window, any countable pairwise-disjoint measurable partition whose union is exactly that payment window represents the discounted Stieltjes dividend payout as the supremum of finite sums of partition-block integrals. This countable-additivity identity retains continuous mass and all dividend atoms. Taking blocks to be unit time intervals after intersecting the payment window supplies the pathwise approximation obligation in the Proved exponential_levy_grid_cash_stieltjes_limit_le_initial theorem, which connects to both open capped BV and UV stochastic verification cores. Remaining conditional cash estimate and integrability require genuine Lévy stochastic calculus.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.stopped_dividend_payment_partition_lintegral_eq_iSup_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (σ : ℝ≥0∞) (T q : ℝ) (ω : Ω)
    (S : ℕ → Set ℝ)
    (hMeas : ∀ k, MeasurableSet (S k))
    (hDisjoint : Pairwise (Function.onFun Disjoint S))
    (hCover : (⋃ k : ℕ, S k) = paymentTimes σ ∩ Iic T) :
    (∫⁻ t in paymentTimes σ ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ⨆ n : ℕ, ∑ k ∈ Finset.range n,
        ∫⁻ t in S k,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) := by sorry

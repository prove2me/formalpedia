-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_compensated_lintegral_tendsto
-- name    : AvramDividend.Classical.negative_compensated_lintegral_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T21:46:59.454207+00:00
-- url     : https://prove2.me/theorems/70431897-f32f-4ad9-8db4-5ec9e6b37ec2
-- title:
--   Monotone convergence of compensated negative-jump Laplace integrals
-- statement:
--   For an arbitrary Borel measure on real jumps supported almost everywhere on strictly negative values, the extended nonnegative integral of the compensated exponential kernel (exp((n+1)y)−1−(n+1)y)/(n+1) converges as n→∞ to the extended absolute first moment ∫|y|dν, even when that moment and measure are infinite. This supplies the exact monotone-convergence step for the non-Gaussian infinite-small-jump-moment Lévy exponent.
-- source:
--   The Prove2Me-Proved exp_negative_compensated_secant_limit; the separately published exp_negative_compensated_secant_mono proof under verification; and pinned Mathlib MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone in MeasureTheory/Integral/Lebesgue/Add.lean. No global dominated convergence or integrable first-moment assumption.

import Mathlib

open MeasureTheory Filter

theorem AvramDividend.Classical.negative_compensated_lintegral_tendsto (ν : Measure ℝ)
    (hneg : ∀ᵐ y ∂ν, y < 0) :
    Filter.Tendsto
      (fun n : ℕ => ∫⁻ y : ℝ,
        ENNReal.ofReal
          ((Real.exp (((n : ℝ) + 1) * y) - 1 -
            ((n : ℝ) + 1) * y) / ((n : ℝ) + 1)) ∂ν)
      Filter.atTop
      (nhds (∫⁻ y : ℝ, ENNReal.ofReal |y| ∂ν)) := by sorry

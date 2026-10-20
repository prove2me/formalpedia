-- Prove2me | Theorems.Thm_AvramDividend_Classical_independence_of_pointwise_limit_real
-- name    : AvramDividend.Classical.independence_of_pointwise_limit_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:23:59.089804+00:00
-- url     : https://prove2.me/theorems/18882c44-7130-47f6-aad2-913f39ced22c
-- title:
--   Independence of real random variables from a sigma algebra survives a pointwise limit
-- statement:
--   For a probability measure and a fixed sub-sigma-algebra m, suppose measurable real random variables Z_n are each independent of m, and Z_n converges pointwise to a measurable real random variable z. Then z is independent of m. Prove using the pinned Mathlib bounded-continuous-test characterisation of independence, its setIntegral factorisation and dominated convergence. This is the exact probabilistic limit-stability principle required to transfer Lévy increment independence from F_u to the right-continuous past F_{s+} as u decreases to s.
-- source:
--   Pinned Mathlib Probability.Independence.BoundedContinuousFunction.indep_comap_of_bcf, Indep.setIntegral_eq_mul and MeasureTheory.tendsto_integral_of_dominated_convergence.

import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory ProbabilityTheory Filter Topology

theorem AvramDividend.Classical.independence_of_pointwise_limit_real
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (Z : ℕ → Ω → ℝ) (z : Ω → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hz : Measurable z)
    (hi : ∀ n, Indep (MeasurableSpace.comap (Z n) inferInstance) m P)
    (ht : ∀ ω, Tendsto (fun n => Z n ω) atTop (𝓝 (z ω))) :
    Indep (MeasurableSpace.comap z inferInstance) m P := by sorry

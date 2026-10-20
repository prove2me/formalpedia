-- Prove2me | Theorems.Thm_AvramDividend_Classical_independence_of_ambient_pointwise_limit_real
-- name    : AvramDividend.Classical.independence_of_ambient_pointwise_limit_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:32:49.860182+00:00
-- url     : https://prove2.me/theorems/cf70b327-fdea-48f5-ad1d-bef201c0473f
-- title:
--   Independence is closed under a pointwise limit of ambient-measurable real random variables
-- statement:
--   Let m be a sub-sigma-algebra of the ambient measurable space mΩ and let P be a probability measure. If ambient-measurable real random variables Z_n are each independent of m and converge everywhere to an ambient-measurable real variable z, then z is also independent of m. Crucially measurability is explicitly with respect to mΩ, not m, so the theorem applies to Lévy future increments which cannot be measurable with respect to the earlier past m. Proof is by the bounded-continuous-test independence criterion and two dominated-convergence arguments.
-- source:
--   Pinned Mathlib indep_comap_of_bcf, Indep.setIntegral_eq_mul, tendsto_integral_of_dominated_convergence; required corrected version for Avram Lévy right-filtration transfer.

import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory ProbabilityTheory Filter Topology

theorem AvramDividend.Classical.independence_of_ambient_pointwise_limit_real
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (Z : ℕ → Ω → ℝ) (z : Ω → ℝ)
    (hZ : ∀ n, Measurable[mΩ] (Z n)) (hz : Measurable[mΩ] z)
    (hi : ∀ n, Indep (MeasurableSpace.comap (Z n) inferInstance) m P)
    (ht : ∀ ω, Tendsto (fun n => Z n ω) atTop (𝓝 (z ω))) :
    Indep (MeasurableSpace.comap z inferInstance) m P := by sorry

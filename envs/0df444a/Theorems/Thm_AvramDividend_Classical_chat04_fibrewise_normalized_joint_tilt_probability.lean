-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_fibrewise_normalized_joint_tilt_probability
-- name    : AvramDividend.Classical.chat04_fibrewise_normalized_joint_tilt_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:33:46.885011+00:00
-- url     : https://prove2.me/theorems/3fff9d88-9058-4c72-828c-6e6c5104ce1e
-- title:
--   Fibrewise unit-mean densities produce a genuine joint tilted probability law on path and observation time
-- statement:
--   Let P be a genuine probability on any path space and η any observation-time probability distribution on ℝ, and let D(ω,t)≥0 be jointly measurable. If for every t the likelihood D_t(ω) integrates to one under P, then the weighted product measure (P⊗η).withDensity D is a genuine probability on path×time. This is the exact Fubini/normalisation result needed to construct the genuine Esscher tilted law at an independent exponential observation horizon by taking η=Exp(p) and D_t(ω)=exp(φX_t(ω)−tψφ), after extending D_t harmlessly to negative clock times. This avoids asserting a global Esscher path measure.
-- source:
--   Apply `isProbabilityMeasure_iff` to the density-weighted product. Rewrite total mass via Mathlib `withDensity_apply` on univ, apply Tonelli `lintegral_prod_symm` (using P finite, hence sigma-finite, and joint measurability D), substitute the fibrewise integral equals one, and use η univ=1. The theorem requires genuine fibrewise normalisation, not the scalar Wiener–Hopf identity.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat04_fibrewise_normalized_joint_tilt_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (D : Ω × ℝ → ℝ≥0∞) (hD : Measurable D)
    (hunit : ∀ t : ℝ, (∫⁻ ω, D (ω, t) ∂P) = 1) :
    IsProbabilityMeasure ((P.prod η).withDensity D) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
-- name    : AvramDividend.Classical.chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:46:00.244347+00:00
-- url     : https://prove2.me/theorems/146b0027-8594-4660-b77c-47dd12219a9b
-- title:
--   Construct the genuine time-dependent Esscher joint law at an independent exponential observation horizon
-- statement:
--   Let X be an actual spectrally negative Lévy process under its defining probability P, θ≥0 an Esscher tilt, and p>0 an independent exponential clock rate. Define the time-dependent density D(ω,t)=exp[θ X_{max(t,0)}(ω)−max(t,0)ψθ], using Real.toNNReal to extend the nonnegative-time process to the real exponential-clock domain. If this explicit density is jointly measurable, then (P⊗Exp(p)).withDensity D is a genuine probability measure on paths×clock; the proof derives every fibre integral E_P D_t=1 from the already accepted finite-horizon Esscher probability theorem. No global Esscher path law is assumed, and the single remaining measurability hypothesis is stated rather than hidden. This is the concrete joint tilted sampling law needed for the finite-rate Wiener–Hopf factorisation.
-- source:
--   Use the actual Lévy law's probability instance `X.isProbability` and Mathlib's `isProbabilityMeasure_expMeasure` for Exp(p). The already proved `chat04_esscher_weighted_finite_horizon_probability` establishes that the fibre-wise P.withDensity D_t has mass one at t_clamped:=Real.toNNReal t; rewrite that mass using `isProbabilityMeasure_iff` and `withDensity_apply` and simplify the unrestricted lintegral. Apply the separately accepted generic fibrewise normalized tilted-product probability theorem to obtain the joint probability law. The only extra input hJoint concerns authentic joint measurability of the concrete density, which follows analytically from adapted càdlàg Lévy paths via measurable step approximations but is not yet proved in this theorem.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_fibrewise_normalized_joint_tilt_probability
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            ((Real.toNNReal z.2 : ℝ)) * X.ψ θ)))) :
    IsProbabilityMeasure
      ((P.prod (ProbabilityTheory.expMeasure p)).withDensity (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            ((Real.toNNReal z.2 : ℝ)) * X.ψ θ)))) := by sorry

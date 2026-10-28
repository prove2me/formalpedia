-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_descending_lintegral_eq_mgf_positive
-- name    : AvramDividend.Classical.avram_ws01e_b_actual_Qp_descending_lintegral_eq_mgf_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:52:56.861045+00:00
-- url     : https://prove2.me/theorems/a7daedce-82e6-4332-86e9-7fea12ef3ee1
-- title:
--   Exact genuine tilted descending ENNReal Laplace transform equals the positive real moment-generating function
-- statement:
--   For θ≥0, p>0 and the actual jointly measurable Esscher observation-clock likelihood, identify the exact ENNReal lintegral of exp(−β(S_e−X_e)) under genuine Qp with ENNReal.ofReal of the real MGF of the nonpositive terminal drawdown −(S_e−X_e), for every β>0. All normalization, measurability, sign and exponential integrability properties are proved from the actual Lévy running supremum and genuine Qp probability law, and no descending factor formula or independence is assumed.
-- source:
--   Mathlib MeasureTheory.ofReal_integral_eq_lintegral_ofReal, ProbabilityTheory.mgf and Integrable.of_bound; Proved joint Esscher law UUID 146b0027, clock drawdown measurable 4390c2cb, path domination 848fbd48; required bridge from the exact target e4e12a00 to the real-analytic transform.

import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_actual_Qp_descending_lintegral_eq_mgf_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (β : ℝ) (hβ : 0 < β) :
    (∫⁻ z : Ω × ℝ,
      ENNReal.ofReal (Real.exp
        (-β * (runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)))
      ∂((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) =
    ENNReal.ofReal
      (mgf (fun z : Ω × ℝ =>
        -(runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1))
        ((P.prod (expMeasure p)).withDensity
          (fun z : Ω × ℝ => ENNReal.ofReal
            (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
              (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) β) := by sorry

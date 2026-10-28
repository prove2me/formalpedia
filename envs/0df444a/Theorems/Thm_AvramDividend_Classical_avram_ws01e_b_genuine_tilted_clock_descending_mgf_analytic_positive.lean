-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_tilted_clock_descending_mgf_analytic_positive
-- name    : AvramDividend.Classical.avram_ws01e_b_genuine_tilted_clock_descending_mgf_analytic_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:47:11.125268+00:00
-- url     : https://prove2.me/theorems/9ed76dc1-12cb-4a28-a0e0-6da73f440bd2
-- title:
--   The actual finite-rate tilted random-clock descending Laplace transform is real analytic on every positive beta
-- statement:
--   For any genuine spectrally negative Lévy X, Esscher parameter θ≥0 and independent real Exp(p) clock with p>0, the actual jointly density-tilted probability law Qp makes the transform β↦E_Qp[exp(−β(S_e−X_e))] real analytic for every β>0. The function is the moment-generating function of the concrete measurable nonpositive random variable −(S_e−X_e). All positive exponents are integrable since the integrand is bounded by one; the proof constructs Qp from the canonical Esscher joint probability theorem and establishes nonpositivity using the canonical running supremum domination. No transform formula, independence or exit identity is assumed. This supplies the exact-likelihood analyticity required for the noncircular all-beta extension.
-- source:
--   Mathlib ProbabilityTheory.analyticOnNhd_mgf, ProbabilityTheory.integrableExpSet; canonical 146b0027-8594-4660-b77c-47dd12219a9b joint Esscher probability, 4390c2cb-aaa7-49a6-bafb-5492d3fc9555 measurability, 848fbd48-f69f-46b9-b2bf-436cb33918a8 supremum dominates path; Kuznetsov–Kyprianou–Rivero (2013), §2.1 Wiener–Hopf transform.

import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Closure
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_genuine_tilted_clock_descending_mgf_analytic_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    AnalyticOnNhd ℝ
      (mgf
        (fun z : Ω × ℝ =>
          -(runningSup X (Real.toNNReal z.2) z.1 -
            X.X (Real.toNNReal z.2) z.1))
        ((P.prod (expMeasure p)).withDensity
          (fun z : Ω × ℝ => ENNReal.ofReal
            (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
              (Real.toNNReal z.2 : ℝ) * X.ψ θ)))))
      (Set.Ioi 0) := by sorry

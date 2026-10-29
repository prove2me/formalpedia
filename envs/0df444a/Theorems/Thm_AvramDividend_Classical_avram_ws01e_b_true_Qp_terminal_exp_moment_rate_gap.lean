-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_Qp_terminal_exp_moment_rate_gap
-- name    : AvramDividend.Classical.avram_ws01e_b_true_Qp_terminal_exp_moment_rate_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T20:14:54.812251+00:00
-- url     : https://prove2.me/theorems/8b26b52f-49ed-43dc-b2ab-0f9b325f38a3
-- title:
--   Genuine random-terminal Esscher Lévy terminal exponential moment at every positive moment-rate gap
-- statement:
--   For the genuine tilted random-terminal law Qp formed by weighting the actual spectrally negative Lévy path and independent Exp(p) clock by exp(phi X_e−q e) with q=psi(phi)>0, and every beta≥0 with psi(phi+beta)−q<p, the terminal exponential moment satisfies (p−(psi(phi+beta)−q)) E_Qp[exp(beta X_e)] = p, in exact ENNReal lintegral form without assuming integrability of the original unweighted variable. This is the actual Qp terminal moment required on beta in (0,lambda_p) to divide by the independently Proved tilted exponential supremum moment and derive the descending Wiener–Hopf strip identity. The finite moment-rate gap is explicit and is discharged from the positive unique shifted root by strict monotonicity. No synthetic moment independence hypothesis or infinite-rate shortcut is used.
-- source:
--   Proved source-specific deterministic Esscher terminal increment full Laplace domain 883afe6f; original independent exponential-clock terminal moment 3281a368; exponential density rate shift 61f61f32; true Qp clock marginal 0ee3767d; Kuznetsov–Kyprianou–Rivero (2013) §2.1 Esscher exponent and exponential resolvent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_true_Qp_terminal_exp_moment_rate_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q p β : ℝ)
    (hφ : 0 < φ) (hq : 0 < q) (hroot : X.ψ φ = q)
    (hp : 0 < p) (hβ : 0 ≤ β)
    (hgap : X.ψ (φ + β) - q < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    ENNReal.ofReal (p - (X.ψ (φ + β) - q)) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal
          (Real.exp (β * X.X (Real.toNNReal z.2) z.1))
        ∂((P.prod (ProbabilityTheory.expMeasure p)).withDensity
          (fun z : Ω × ℝ => ENNReal.ofReal
            (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
              (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) =
      ENNReal.ofReal p := by sorry

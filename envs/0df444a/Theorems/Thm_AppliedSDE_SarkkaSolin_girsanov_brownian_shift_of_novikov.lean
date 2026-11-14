-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_girsanov_brownian_shift_of_novikov
-- name    : AppliedSDE.SarkkaSolin.girsanov_brownian_shift_of_novikov
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:57:29.348366+00:00
-- url     : https://prove2.me/theorems/5816a8df-d14f-458f-8c72-e64ce25fbb78
-- title:
--   Scalar Girsanov I from Novikov's exponential-moment criterion
-- statement:
--   Original rigorous strengthening derived from Särkkä and Solin (2019), Theorem 7.7, equations (7.43)–(7.46), printed p. 107. Let θ be a progressively measurable square-integrable scalar drift, zero after a fixed T>0, and W Brownian relative to its filtration. Assume the Novikov exponential-moment condition E exp((1/2)∫_0^T θ_t²dt)<∞. Prove that the stochastic exponential density Z_T has expectation one, that the Radon–Nikodym weighted measure is a probability, and that W−∫θdt is Brownian under that measure. This supplies a sufficient condition for the density normalisation assumed by Theorem 7.8. It corrects the source's heuristic use of mere L² integrability without falsely claiming exact verbatim equivalence to the printed assumptions.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \mathbb E_P e^{\frac12\int_0^T\theta_t^2\,\mathrm dt}<\infty\ \Longrightarrow\ \mathbb E_P[Z_T]=1
--   $$
-- source:
--   Original derived rigorous strengthening of Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 7.7, equations (7.43)–(7.46), printed p. 107. https://doi.org/10.1017/9781108186735

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology

theorem AppliedSDE.SarkkaSolin.girsanov_brownian_shift_of_novikov
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T : ℝ) (hT : 0 < T)
    (θ : Ω → ℝ → ℝ)
    (hθmeas : Measurable (Function.uncurry θ))
    (hθprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ θ)
    (hθq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖θ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hθzero : ∀ (ω : Ω) (s : ℝ), T ≤ s → θ ω s = 0)
    (Z : Ω → ℝ)
    (hZ : ∀ ω : Ω,
      Z ω = Real.exp (
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW θ hθmeas hθprog hθq T ω -
        (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..T, θ ω s ^ 2))
    (hNovikov : Integrable (fun ω : Ω =>
      Real.exp ((1 / 2 : ℝ) *
        ∫ s in (0 : ℝ)..T, θ ω s ^ 2)) P) :
    let Q : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal (Z ω))
    let shifted : ℝ≥0 → Ω → ℝ := fun t ω =>
      W.W (t : ℝ) ω - ∫ s in (0 : ℝ)..(t : ℝ), θ ω s
    (∫ ω, Z ω ∂P = 1) ∧
      IsProbabilityMeasure Q ∧ IsBrownianReal shifted Q := by
  sorry

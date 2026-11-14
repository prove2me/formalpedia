-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_girsanov_brownian_shift_terminal_density
-- name    : AppliedSDE.SarkkaSolin.girsanov_brownian_shift_terminal_density
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:48:52.420029+00:00
-- url     : https://prove2.me/theorems/5cddf6e0-348d-4542-a41c-d09699726965
-- title:
--   Girsanov change of measure for a stopped scalar adapted drift
-- statement:
--   Let W be standard scalar Brownian motion relative to a filtration and let θ be progressively measurable, square integrable in the required stochastic sense and zero after a deterministic terminal time T. Construct the exponential density from the Brownian stochastic integral of θ and the negative half-integral of θ squared. Assume its terminal expectation is one. Then the measure with that terminal Radon–Nikodym density is a probability measure, and W minus the time integral of θ is standard Brownian motion under the tilted measure. This is the stopped scalar version of Girsanov II. It explicitly requires a true exponential-martingale density and is substantially stronger than a formal path-density ratio.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \frac{\mathrm dQ}{\mathrm dP}=e^{\int_0^T\theta_s\,\mathrm dW_s-\frac12\int_0^T\theta_s^2\,\mathrm ds},\quad W_t^Q=W_t-\int_0^t\theta_s\,\mathrm ds
--   $$
-- source:
--   Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 7.8 and equations (7.47)–(7.49), printed p. 108. https://doi.org/10.1017/9781108186735

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology

theorem AppliedSDE.SarkkaSolin.girsanov_brownian_shift_terminal_density
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
    (hZmean : ∫ ω, Z ω ∂P = 1) :
    let Q : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal (Z ω))
    let shifted : ℝ≥0 → Ω → ℝ := fun t ω =>
      W.W (t : ℝ) ω - ∫ s in (0 : ℝ)..(t : ℝ), θ ω s
    IsProbabilityMeasure Q ∧ IsBrownianReal shifted Q := by
  sorry

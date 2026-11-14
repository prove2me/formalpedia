-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_girsanov_shifted_brownian_core
-- name    : AppliedSDE.SarkkaSolin.girsanov_shifted_brownian_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T23:48:36.47069+00:00
-- url     : https://prove2.me/theorems/7b240172-1718-4bcf-bf9e-17fc19de2e5f
-- title:
--   Girsanov Brownian-law transfer under terminal exponential density
-- statement:
--   For the bounded-horizon Brownian motion setup of AppliedSDE Chapter 7, let Q be the terminal exponential-stochastic-integral density tilt, assumed to have unit mean. Then W(t)-integral_0^t theta(s) ds is Brownian under Q. This is the substantive Brownian-law change-of-measure component of the original Chapter 7 Girsanov theorem 5cddf6e0-348d-4542-a41c-d09699726965. Probability normalisation of Q is handled by the separate published unit-mean-density child. A proof of this Brownian-law theorem requires the true Girsanov martingale/change-of-measure argument and is not supplied by its statement.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 7, Girsanov theorem.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology

theorem AppliedSDE.SarkkaSolin.girsanov_shifted_brownian_core
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
    IsBrownianReal shifted Q := by
  sorry

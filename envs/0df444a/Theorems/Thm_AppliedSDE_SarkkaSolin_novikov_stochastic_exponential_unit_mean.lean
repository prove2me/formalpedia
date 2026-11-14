-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_novikov_stochastic_exponential_unit_mean
-- name    : AppliedSDE.SarkkaSolin.novikov_stochastic_exponential_unit_mean
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T00:33:12.969863+00:00
-- url     : https://prove2.me/theorems/07f6eb01-6ad6-4336-8a23-0a8eda14c532
-- title:
--   Novikov exponential-martingale condition gives unit expectation
-- statement:
--   Under the progressively measurable square-integrable Brownian stochastic-integral assumptions and Novikov integrability of exp(1/2 integral theta^2), prove that the terminal exponential stochastic integral density Z has expectation exactly one. This is the substantive Novikov criterion needed to derive Chapter 7 girsanov_brownian_shift_of_novikov from the terminal-density Girsanov theorem. The child contains no assumption of the desired unit-mean conclusion.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Chapter 7; Novikov martingale criterion.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology

theorem AppliedSDE.SarkkaSolin.novikov_stochastic_exponential_unit_mean
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
    ∫ ω, Z ω ∂P = 1 := by
  sorry

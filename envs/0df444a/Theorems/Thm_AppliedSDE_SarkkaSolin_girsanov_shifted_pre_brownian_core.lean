-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_girsanov_shifted_pre_brownian_core
-- name    : AppliedSDE.SarkkaSolin.girsanov_shifted_pre_brownian_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T17:11:50.11021+00:00
-- url     : https://prove2.me/theorems/cfda093a-3355-4138-b76a-f9966b01a504
-- title:
--   Finite-dimensional Brownian law of the Girsanov drift-shifted process under the exponential-tilted measure
-- statement:
--   After the change of measure Q defined by the unit-mean exponential martingale, the drift-corrected process has all the Brownian finite-dimensional centred Gaussian laws and independent increments. This is the distributional part of the full Girsanov theorem.
-- source:
--   Sarkka and Solin (2019) Girsanov theorem, Chapter 7; Mathlib IsBrownianReal extends IsPreBrownianReal with the cont field.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology

theorem AppliedSDE.SarkkaSolin.girsanov_shifted_pre_brownian_core
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
    IsPreBrownianReal shifted Q := by
  sorry

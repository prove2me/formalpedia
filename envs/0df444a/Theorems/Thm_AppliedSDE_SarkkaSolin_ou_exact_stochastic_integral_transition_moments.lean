-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_ou_exact_stochastic_integral_transition_moments
-- name    : AppliedSDE.SarkkaSolin.ou_exact_stochastic_integral_transition_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:58:17.269992+00:00
-- url     : https://prove2.me/theorems/bc5cda7c-dc7b-488a-b1bd-b5d8f88d30f8
-- title:
--   Ornstein–Uhlenbeck exact stochastic-integral transition mean and variance
-- statement:
--   Särkkä and Solin (2019), Example 6.2 and equations (6.28)–(6.30), printed pp. 80–81. For rate λ>0, diffusion variance q≥0, deterministic initial state x0 and horizon T≥0, define the exact scalar OU solution at time T by exp(−λT)x0 plus the Brownian Itô integral of √q exp(−λ(T−s)) over 0≤s≤T. Prove directly from the genuine stochastic integral that its expectation equals exp(−λT)x0 and its variance equals q/(2λ)(1−exp(−2λT)). This is an actual stochastic moment theorem and a source-derived prerequisite for the Gaussian transition law, stationary OU covariance and GP/Kalman capstone. The further assertion that the full law is Gaussian remains a separate obligation.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \mathbb E[X_T]=e^{-\lambda T}x_0,\quad\operatorname{Var}(X_T)=\frac q{2\lambda}(1-e^{-2\lambda T})
--   $$
-- source:
--   Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Example 6.2, equations (6.28)–(6.30), printed pp. 80–81. https://doi.org/10.1017/9781108186735

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology BigOperators

theorem AppliedSDE.SarkkaSolin.ou_exact_stochastic_integral_transition_moments
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (rate q x₀ T : ℝ) (hrate : 0 < rate) (hq : 0 ≤ q) (hT : 0 ≤ T)
    (H : Ω → ℝ → ℝ)
    (hH : ∀ (ω : Ω) (s : ℝ),
      H ω s = Real.sqrt q * Real.exp (-rate * (T - s)))
    (hHmeas : Measurable (Function.uncurry H))
    (hHprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHsq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    let Y : Ω → ℝ := fun ω =>
      Real.exp (-rate * T) * x₀ +
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
          W ℱ hW H hHmeas hHprog hHsq T ω
    (∫ ω, Y ω ∂P) = Real.exp (-rate * T) * x₀ ∧
      (∫ ω, (Y ω - Real.exp (-rate * T) * x₀) ^ 2 ∂P) =
        q / (2 * rate) * (1 - Real.exp (-2 * rate * T)) := by
  sorry

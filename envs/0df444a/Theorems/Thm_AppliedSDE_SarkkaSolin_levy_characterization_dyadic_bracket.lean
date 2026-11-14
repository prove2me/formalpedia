-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_levy_characterization_dyadic_bracket
-- name    : AppliedSDE.SarkkaSolin.levy_characterization_dyadic_bracket
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:47:58.459818+00:00
-- url     : https://prove2.me/theorems/d013d31d-da10-4236-bb0f-65f6240bd519
-- title:
--   Lévy martingale characterisation of Brownian motion from dyadic quadratic variation
-- statement:
--   A real-valued process W indexed by nonnegative time on a probability space starts at zero, has continuous sample paths, is adapted and integrable, and is a martingale relative to a filtration. Assume for each fixed terminal time the sum of squared increments along uniform dyadic partitions converges in probability to the elapsed time. Lévy's characterisation asserts W is standard Brownian motion. The quadratic-variation hypothesis is stated using actual dyadic increments and convergence in probability, rather than introducing an arbitrary bracket function unrelated to W.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \sum_{k=0}^{2^m-1}\left(W_{(k+1)t/2^m}-W_{kt/2^m}\right)^2\xrightarrow{\mathbb P}t
--   $$
-- source:
--   Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (2019), Theorem 7.2 and Equation (7.11), printed p. 100. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

theorem AppliedSDE.SarkkaSolin.levy_characterization_dyadic_bracket
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → ℝ)
    (hW0 : ∀ ω : Ω, W 0 ω = 0)
    (hcont : ∀ ω : Ω, Continuous (fun t : ℝ≥0 => W t ω))
    (hadapt : ∀ t : ℝ≥0, Measurable[ℱ t] (W t))
    (hint : ∀ t : ℝ≥0, Integrable (W t) P)
    (hmart : ∀ (s t : ℝ≥0), s ≤ t →
      P[W t | ℱ s] =ᵐ[P] W s)
    (hQV : ∀ (t : ℝ≥0) (ε : ℝ), 0 < ε →
      Tendsto (fun n : ℕ =>
        P {ω : Ω | ε ≤ abs (
          (∑ k ∈ Finset.range (2 ^ n),
            (W (((k + 1 : ℕ) : ℝ≥0) * t / (2 ^ n : ℕ)) ω -
             W ((k : ℝ≥0) * t / (2 ^ n : ℕ)) ω) ^ 2) - t.toReal)})
        atTop (𝓝 0)) :
    IsBrownianReal W P := by
  sorry

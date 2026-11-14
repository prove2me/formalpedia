-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_exact_rejection_sampling_accepted_law
-- name    : AppliedSDE.SarkkaSolin.exact_rejection_sampling_accepted_law
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:56:45.374264+00:00
-- url     : https://prove2.me/theorems/abc82f18-47fe-43a7-853c-18d275099080
-- title:
--   Exact rejection sampling has the prescribed weighted accepted law
-- statement:
--   Original derived from the exact diffusion rejection algorithm of Särkkä and Solin (2019), Algorithm 8.23. Given a proposal probability P on paths or finite skeletons and a measurable acceptance weight 0≤w≤1, sample the proposal together with an independent uniform mark and accept exactly when the mark lies beneath w. Under positive mean acceptance probability, the conditional law of accepted proposals on each measurable event A is ∫_A w dP divided by ∫w dP. This establishes the general exact rejection-sampling change of law behind the Poisson-void event; identifying the weight with the source SDE path-law Radon–Nikodym factor and proving Brownian bridge reconstruction are separate obligations.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   Q(A)=\frac{\int_A w(x)\,P(\mathrm dx)}{\int w(x)\,P(\mathrm dx)}
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Algorithm 8.23 and Theorem 8.22, equation (8.130), printed pp. 159–160. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem AppliedSDE.SarkkaSolin.exact_rejection_sampling_accepted_law
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (weight : Ω → ℝ) (hweight : Measurable weight)
    (hbound : ∀ ω : Ω, 0 ≤ weight ω ∧ weight ω ≤ 1)
    (hpositive : 0 < ∫ ω, weight ω ∂P)
    (A : Set Ω) (hA : MeasurableSet A) :
    let U : Measure ℝ :=
      (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)
    let joint : Measure (Ω × ℝ) := P.prod U
    let accept : Set (Ω × ℝ) := {z | z.2 ≤ weight z.1}
    (joint.restrict accept).real (A ×ˢ Set.univ) /
      (joint.restrict accept).real Set.univ =
        (∫ ω in A, weight ω ∂P) / (∫ ω, weight ω ∂P) := by
  sorry

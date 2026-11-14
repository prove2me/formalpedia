-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_path_likelihood_radon_nikodym_expectation
-- name    : AppliedSDE.SarkkaSolin.path_likelihood_radon_nikodym_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:56:18.662223+00:00
-- url     : https://prove2.me/theorems/6ceb30e2-848b-4a1b-a8b6-6e828966d0f1
-- title:
--   Path-functional likelihood weighting under an exact Radon–Nikodym density
-- statement:
--   Original derived from Theorem 7.4 and the rigorous Radon–Nikodym interpretation of diffusion path likelihood ratios (printed pp. 105–108). Let P be the reference path-law measure and Z≥0 a measurable integrable density with E_P[Z]=1. The tilted law Q=P.withDensity Z is a probability measure, and each integrable path functional has Q expectation equal to its P expectation weighted by Z. This is the general path-functional meaning of the textbook's formal path-density ratio. Expressing Z itself as the stochastic exponential of a diffusion drift change is a separate Girsanov theorem already drafted in the proposal.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   \mathbb E_Q[F]=\mathbb E_P[ZF],\qquad \frac{\mathrm dQ}{\mathrm dP}=Z
--   $$
-- source:
--   Original derived from Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Theorem 7.4, path-law likelihood ratio and Radon–Nikodym interpretation, printed pp. 105–108. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem AppliedSDE.SarkkaSolin.path_likelihood_radon_nikodym_expectation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZmeas : Measurable Z)
    (hZnonneg : ∀ ω : Ω, 0 ≤ Z ω)
    (hZintegrable : Integrable Z P)
    (hZmean : ∫ ω, Z ω ∂P = 1)
    (F : Ω → ℝ) (hFmeas : Measurable F)
    (hFZintegrable : Integrable (fun ω => F ω * Z ω) P) :
    let Q : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal (Z ω))
    IsProbabilityMeasure Q ∧
      (∫ ω, F ω ∂Q) = (∫ ω, F ω * Z ω ∂P) := by
  sorry

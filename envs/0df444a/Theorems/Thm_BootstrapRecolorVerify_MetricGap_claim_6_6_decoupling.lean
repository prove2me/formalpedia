-- Prove2me | Theorems.Thm_BootstrapRecolorVerify_MetricGap_claim_6_6_decoupling
-- name    : BootstrapRecolorVerify.MetricGap.claim_6_6_decoupling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:36:07.521679+00:00
-- url     : https://prove2.me/theorems/bcb99ace-858d-439e-b724-d3e3b50190e6
-- title:
--   Claim 6.6 — Metric decoupling
-- statement:
--   Let $(X,Y)$ be an arbitrary pair of random points in a pseudometric space (in particular, any metric space), and let $X',Y'$ be independent of each other and of the pair, with the respective marginal laws of $X,Y$. For measurable random distances, interpreted as extended nonnegative expectations,
--
--   $$\mathbb E\rho(X',Y')\le\mathbb E\rho(X,Y)+\frac12\mathbb E\rho(X,X')+\frac12\mathbb E\rho(Y,Y').$$
--
--   Dependence within $(X,Y)$ is allowed. There is no finite-support, finite-moment, separability or completeness assumption. This metric inequality compares the independent-pair cost with a coupled cost and two within-marginal costs.
--
--   **Formalization Note** The joint law is an arbitrary probability measure $\mu$ on $S\times S$ equipped with the product of the Borel sigma algebras. Its marginals $\mu_X,\mu_Y$ give the independent product laws $\mu_X\otimes\mu_Y$, $\mu_X\otimes\mu_X$, and $\mu_Y\otimes\mu_Y$. Almost-everywhere measurability is required for the four distance functions under these laws, so that each displayed expectation has its usual meaning.
--
--   Differences from the source:
--   - generalization: random points in a metric space → random points in any pseudometric space; reason: the inequality uses only symmetry and the triangle inequality, so every metric-space instance is retained; this also covers zero distances between distinct points and the projected distances used in the paper under its p.2 convention
--   - encoding: four random variables with the stated joint independence and marginal laws → the arbitrary joint law μ and the three corresponding products of its marginals; reason: the four expectations depend only on these pair laws, and independent copies are realized on their product space
--   - encoding: expectations of random metric distances → extended nonnegative Lebesgue integrals with explicit almost-everywhere measurability of each distance; reason: this states the usual measurability convention while retaining infinite expected distances and arbitrary metric spaces
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), Claim 6.6, p.25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=25; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace BootstrapRecolorVerify.MetricGap

/-- Claim 6.6, p.25, in joint-law form, also allowing pseudometrics. μ is the joint law of (X,Y).
The product of its marginals is the law of the independent copies (X',Y').
The other two product laws describe (X,X') and (Y,Y'). Measurability means
exactly that the four expectations in the source are defined. No countability,
separability, completeness or finite-moment condition is imposed. -/
theorem claim_6_6_decoupling {S : Type*} [PseudoMetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure (S × S)) [IsProbabilityMeasure μ]
    (hXY : AEMeasurable (fun p : S × S => edist p.1 p.2) μ)
    (hind : AEMeasurable (fun p : S × S => edist p.1 p.2)
      ((μ.map Prod.fst).prod (μ.map Prod.snd)))
    (hXX : AEMeasurable (fun p : S × S => edist p.1 p.2)
      ((μ.map Prod.fst).prod (μ.map Prod.fst)))
    (hYY : AEMeasurable (fun p : S × S => edist p.1 p.2)
      ((μ.map Prod.snd).prod (μ.map Prod.snd))) :
    (∫⁻ p : S × S, edist p.1 p.2 ∂((μ.map Prod.fst).prod (μ.map Prod.snd))) ≤
      (∫⁻ p : S × S, edist p.1 p.2 ∂μ) +
      (1 / 2 : ℝ≥0∞) *
        (∫⁻ p : S × S, edist p.1 p.2 ∂((μ.map Prod.fst).prod (μ.map Prod.fst))) +
      (1 / 2 : ℝ≥0∞) *
        (∫⁻ p : S × S, edist p.1 p.2 ∂((μ.map Prod.snd).prod (μ.map Prod.snd))) := by sorry

end BootstrapRecolorVerify.MetricGap

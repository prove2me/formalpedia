-- Prove2me | Theorems.Thm_DistCov_Indep_proposition_3_5
-- name    : DistCov.Indep.proposition_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:24.517158+00:00
-- url     : https://prove2.me/theorems/86ad01f6-d515-49c4-a934-0c1a6e30795f
-- title:
--   Proposition 3.5 — a_µ(x) = ‖ϕ(x) − β_ϕ(µ)‖² + D(µ)/2, D(µ) = 2Var(ϕ(X)), d_µ = −2⟨ϕ − β, ϕ′ − β⟩
-- statement:
--   Let $\mathcal X$ be a separable metric space with its Borel $\sigma$-field, with negative type witnessed by the embedding $\phi:\mathcal X\to H$ into a real Hilbert space ($d(x,x')=\|\phi(x)-\phi(x')\|^2$), and let $\mu$ be a probability measure on $\mathcal X$ with finite first moment. Write $\beta_\phi(\mu)=\int\phi\,d\mu$. Then:
--
--   1. for all $x\in\mathcal X$, $$a_\mu(x)=\|\phi(x)-\beta_\phi(\mu)\|^2+D(\mu)/2;$$
--   2. $D(\mu)=2\operatorname{Var}(\phi(X))$ if $X\sim\mu$, where $\operatorname{Var}(Z)=\mathbf E\|Z-\mathbf E Z\|^2$, that is $$D(\mu)=2\int\|\phi(x)-\beta_\phi(\mu)\|^2\,d\mu(x);$$
--   3. for all $x,x'\in\mathcal X$, $$d_\mu(x,x')=-2\,\big\langle\phi(x)-\beta_\phi(\mu),\,\phi(x')-\beta_\phi(\mu)\big\rangle.$$
--
--   The third identity expresses the centred distance $d_\mu$ as a (negative) Gram kernel of the centred embedding; it is what turns $\operatorname{dcov}(\theta)$ into a squared norm in Proposition 3.7.
--
--   **Formalization Note** The variance is written out as the integral of $\|\phi(x)-\beta_\phi(\mu)\|^2$, since $\mathbf E[\phi(X)]=\beta_\phi(\mu)$. Hilbert spaces are real (Errata (viii), p. 27); separability is the standing assumption of Errata (i), p. 24.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 13, Proposition 3.5 and the definition of Var(Z) before it; Errata (i), p. 24 and (viii), p. 27

import Mathlib
import Definitions.Def_DistCov_Indep_Setting

namespace DistCov.Indep

open MeasureTheory
open scoped InnerProductSpace

theorem proposition_3_5 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ)
    (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ) :
    (∀ x, meanDist μ x = ‖ϕ x - bary ϕ μ‖ ^ 2 + D μ / 2) ∧
    D μ = 2 * ∫ x, ‖ϕ x - bary ϕ μ‖ ^ 2 ∂μ ∧
    (∀ x x', dcent μ x x' = -2 * ⟪ϕ x - bary ϕ μ, ϕ x' - bary ϕ μ⟫_ℝ) := by sorry

end DistCov.Indep

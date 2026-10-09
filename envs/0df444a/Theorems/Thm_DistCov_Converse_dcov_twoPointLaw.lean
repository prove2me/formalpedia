-- Prove2me | Theorems.Thm_DistCov_Converse_dcov_twoPointLaw
-- name    : DistCov.Converse.dcov_twoPointLaw
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:27:22.837626+00:00
-- url     : https://prove2.me/theorems/d5f4bf18-5d91-43a4-a4eb-de73905933de
-- title:
--   Proof of Proposition 3.15, p. 17, first display — dcov((µ₁ × δ(y₁) + µ₂ × δ(y₂))/2) = −d(y₁, y₂) D(µ₁ − µ₂)/8
-- statement:
--   Let $\mathcal X$ and $\mathcal Y$ be separable metric spaces, let $\mu_1,\mu_2$ be Borel probability measures on $\mathcal X$ with finite first moments, and let $y_1\neq y_2$ be points of $\mathcal Y$. Put
--   $$\theta:=\tfrac12\big(\mu_1\times\delta(y_1)+\mu_2\times\delta(y_2)\big).$$
--   Then
--   $$\operatorname{dcov}(\theta)=-\frac{d(y_1,y_2)\,D(\mu_1-\mu_2)}{8}.$$
--
--   In the paper this identity is used twice: with $D(\mu_1-\mu_2)>0$ it gives a law with negative distance covariance, and with $D(\mu_1-\mu_2)=0$ a law with zero distance covariance. The sign of $D(\mu_1-\mu_2)$ is not assumed here.
--
--   **Formalization Note.** Separability of both spaces is the standing assumption of Errata (i). The marginals of $\theta$ are $(\mu_1+\mu_2)/2$ and $(\delta(y_1)+\delta(y_2))/2$ and have finite first moments, so all integrals in $\operatorname{dcov}(\theta)$ are genuine. The hypothesis $y_1\neq y_2$ is kept as on the page, although the identity also holds (with both sides $0$) when $y_1=y_2$.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 17, proof of Proposition 3.15, first display

import Mathlib
import Definitions.Def_DistCov_Converse_Setting

open MeasureTheory

namespace DistCov.Converse

theorem dcov_twoPointLaw
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (μ₁ μ₂ : Measure X) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁ : DistCov.Indep.FiniteFirstMoment μ₁) (hμ₂ : DistCov.Indep.FiniteFirstMoment μ₂)
    (y₁ y₂ : Y) (hy : y₁ ≠ y₂) :
    DistCov.Indep.dcov (twoPointLaw μ₁ μ₂ y₁ y₂) = -(dist y₁ y₂) * DistCov.Indep.Ddiff μ₁ μ₂ / 8 := by sorry

end DistCov.Converse

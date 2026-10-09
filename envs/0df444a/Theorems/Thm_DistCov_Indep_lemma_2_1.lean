-- Prove2me | Theorems.Thm_DistCov_Indep_lemma_2_1
-- name    : DistCov.Indep.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:00.395999+00:00
-- url     : https://prove2.me/theorems/0d01b838-1af8-4797-9349-0965c8a5488b
-- title:
--   Lemma 2.1 — if µ has finite first moment then d_µ ∈ L²(µ × µ)
-- statement:
--   Let $(\mathcal X,d)$ be a separable metric space with its Borel $\sigma$-field, and let $\mu$ be a probability measure on $\mathcal X$ with a finite first moment, i.e. $d(x,x')\in L^1(\mu\times\mu)$. Let $d_\mu(x,x')=d(x,x')-a_\mu(x)-a_\mu(x')+D(\mu)$ be the centred distance, where $a_\mu(x)=\int d(x,x')\,d\mu(x')$ and $D(\mu)=\int d\,d\mu^2$. Then
--   $$d_\mu(x,x')\in L^2(\mu\times\mu).$$
--
--   The lemma says that centring the distance improves its integrability from $L^1$ to $L^2$. Together with the Cauchy–Schwarz inequality it is what makes the distance covariance $\operatorname{dcov}(\theta)$ a well-defined finite number under first-moment assumptions alone.
--
--   **Formalization Note** The page says "Let $\mathcal X$ be any metric space"; separability (`SecondCountableTopology`) and the Borel $\sigma$-field are the standing assumption added by the author in Errata (i), p. 24, which makes $(x,x')\mapsto d(x,x')$ measurable for the product $\sigma$-field. Membership in $L^2$ is Mathlib's `MemLp … 2`, which includes a.e. strong measurability.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 4, Lemma 2.1 (proof display corrected by Errata (ii), p. 24); Errata (i), p. 24

import Mathlib
import Definitions.Def_DistCov_Indep_Setting

namespace DistCov.Indep

open MeasureTheory

theorem lemma_2_1 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ] (h : FiniteFirstMoment μ) :
    MemLp (fun p : X × X => dcent μ p.1 p.2) 2 (μ.prod μ) := by sorry

end DistCov.Indep

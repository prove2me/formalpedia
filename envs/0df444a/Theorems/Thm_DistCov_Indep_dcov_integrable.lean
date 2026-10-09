-- Prove2me | Theorems.Thm_DistCov_Indep_dcov_integrable
-- name    : DistCov.Indep.dcov_integrable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:01.134358+00:00
-- url     : https://prove2.me/theorems/d470305d-d3b6-49cf-a68c-d645588e3108
-- title:
--   p. 4 — δ_θ is θ²-integrable, so dcov(θ) is defined
-- statement:
--   Let $\mathcal X$ and $\mathcal Y$ be separable metric spaces with their Borel $\sigma$-fields, and let $\theta$ be a probability measure on $\mathcal X\times\mathcal Y$ whose marginals $\mu$ on $\mathcal X$ and $\nu$ on $\mathcal Y$ have finite first moments. Then the function
--   $$\delta_\theta\big((x,y),(x',y')\big)=d_\mu(x,x')\,d_\nu(y,y')$$
--   is integrable with respect to $\theta^2=\theta\times\theta$, so that
--   $$\operatorname{dcov}(\theta)=\int\delta_\theta\,d\theta^2$$
--   is a well-defined real number.
--
--   This is the sentence of p. 4 that defines distance covariance ("By Lemma 2.1 and the Cauchy–Schwarz inequality, we may define…"); it is stated as a theorem so that every later statement about $\operatorname{dcov}(\theta)$ is about a genuine integral.
--
--   **Formalization Note** Separability and the Borel $\sigma$-fields are the standing assumption of Errata (i), p. 24. The marginals are the push-forwards of $\theta$ under the two projections.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 4, definition of dcov(θ) (the sentence 'By Lemma 2.1 and the Cauchy–Schwarz inequality, we may define'); Errata (i), p. 24

import Mathlib
import Definitions.Def_DistCov_Indep_Setting

namespace DistCov.Indep

open MeasureTheory

theorem dcov_integrable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (θ : Measure (X × Y)) [IsProbabilityMeasure θ]
    (hμ : FiniteFirstMoment (θ.map Prod.fst)) (hν : FiniteFirstMoment (θ.map Prod.snd)) :
    Integrable (fun pq : (X × Y) × (X × Y) =>
      dcent (θ.map Prod.fst) pq.1.1 pq.2.1 * dcent (θ.map Prod.snd) pq.1.2 pq.2.2) (θ.prod θ) := by sorry

end DistCov.Indep

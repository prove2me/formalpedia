-- Prove2me | Theorems.Thm_DistCov_Indep_theorem_3_11
-- name    : DistCov.Indep.theorem_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:10.11901+00:00
-- url     : https://prove2.me/theorems/17d82b1e-ecfb-440c-91e7-99335f7dac2d
-- title:
--   Theorem 3.11 — on spaces of strong negative type, dcov(θ) = 0 implies θ is a product measure
-- statement:
--   Let $\mathcal X$ and $\mathcal Y$ be separable metric spaces with their Borel $\sigma$-fields, both of strong negative type, and let $\theta$ be a probability measure on $\mathcal X\times\mathcal Y$ whose marginals $\mu$ on $\mathcal X$ and $\nu$ on $\mathcal Y$ have finite first moments. If
--   $$\operatorname{dcov}(\theta)=0,$$
--   then $\theta$ is a product measure: $\theta=\mu\times\nu$.
--
--   This is the key result of the theory: on spaces of strong negative type, distance covariance vanishes only under independence, which makes the distance-covariance test of independence consistent against all alternatives.
--
--   **Formalization Note** Strong negative type is defined from (3.1) and the condition "$D(\mu_1-\mu_2)=0$ only when $\mu_1=\mu_2$" (p. 11), not through an embedding. $\operatorname{dcov}(\theta)$ is the integral of $d_\mu(x,x')d_\nu(y,y')$ against $\theta\times\theta$; the finite-first-moment hypotheses on the marginals make it a genuine integral. "Product measure" means equality with the product of the two marginals of $\theta$. Separability (`SecondCountableTopology`) and the Borel $\sigma$-fields are the standing assumption added by the author in Errata (i), p. 24.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 16, Theorem 3.11; Errata (i), p. 24

import Mathlib
import Definitions.Def_DistCov_Indep_Setting

namespace DistCov.Indep

open MeasureTheory

theorem theorem_3_11 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (hX : StrongNegType X) (hY : StrongNegType Y)
    (θ : Measure (X × Y)) [IsProbabilityMeasure θ]
    (hμ : FiniteFirstMoment (θ.map Prod.fst)) (hν : FiniteFirstMoment (θ.map Prod.snd))
    (h : dcov θ = 0) : IsProduct θ := by sorry

end DistCov.Indep

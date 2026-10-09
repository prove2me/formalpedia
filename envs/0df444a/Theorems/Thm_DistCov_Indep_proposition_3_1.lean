-- Prove2me | Theorems.Thm_DistCov_Indep_proposition_3_1
-- name    : DistCov.Indep.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:09.145988+00:00
-- url     : https://prove2.me/theorems/a87643b1-d46a-4d3e-9bea-c334a4e207a0
-- title:
--   Proposition 3.1 — strong negative type iff the barycenter map β_ϕ is injective on probability measures
-- statement:
--   Let $\mathcal X$ be a separable metric space with its Borel $\sigma$-field, and suppose $\mathcal X$ has negative type as witnessed by the embedding $\phi:\mathcal X\to H$ into a real Hilbert space, i.e. $d(x,x')=\|\phi(x)-\phi(x')\|^2$. Then
--   $$\mathcal X\text{ has strong negative type}\iff \beta_\phi\text{ is injective on the probability measures on }\mathcal X\text{ with finite first moment},$$
--   where $\beta_\phi(\mu)=\int\phi\,d\mu$.
--
--   Proposition 3.1 recasts strong negative type, a statement about the energy $D(\mu_1-\mu_2)$, as injectivity of a Hilbert-space-valued mean; this is the form in which strong negative type is used in Lemmas 3.8 and 3.9.
--
--   **Formalization Note** Strong negative type is defined directly from (3.1) and the condition "$D(\mu_1-\mu_2)=0$ only when $\mu_1=\mu_2$" (p. 11), not through an embedding, so the proposition is not definitional. $H$ is any real Hilbert space. Separability is the standing assumption of Errata (i), p. 24.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 11, Proposition 3.1; Errata (i), p. 24

import Mathlib
import Definitions.Def_DistCov_Indep_Setting

namespace DistCov.Indep

open MeasureTheory

theorem proposition_3_1 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ϕ : X → H) (hϕ : IsNegTypeEmbedding ϕ) :
    StrongNegType X ↔ BaryInjProb ϕ := by sorry

end DistCov.Indep

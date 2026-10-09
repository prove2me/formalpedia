-- Prove2me | Theorems.Thm_DistCov_Indep_lemma_3_9
-- name    : DistCov.Indep.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:07.987012+00:00
-- url     : https://prove2.me/theorems/64cf0376-eb3a-411e-ad27-4cb1a7343d2d
-- title:
--   Lemma 3.9 — strong negative type admits an embedding ϕ with β_ϕ injective on M¹(X)
-- statement:
--   Let $\mathcal X$ be a separable metric space with its Borel $\sigma$-field, of strong negative type. Then there exists an embedding $\phi:\mathcal X\to\ell^2(\mathbb N)$, i.e. $d(x,x')=\|\phi(x)-\phi(x')\|^2$ for all $x,x'$, such that the barycenter map $\beta_\phi$ is injective on $M^1(\mathcal X)$, the finite signed measures $\mu$ for which $|\mu|$ has a finite first moment (not merely on the probability measures).
--
--   Injectivity on all of $M^1(\mathcal X)$, rather than on probability measures, is what the independence argument needs: the measure $\theta-\mu\times\nu$ it must detect is a signed measure of total mass $0$.
--
--   **Formalization Note** Injectivity on $M^1(\mathcal X)$ is stated through pairs of finite measures: $\beta_\phi(m_1)=\beta_\phi(m_2)\Rightarrow m_1=m_2$ for finite $m_1,m_2$ with finite first moment (equivalent via the Jordan decomposition and linearity of $\beta_\phi$). The target is $\ell^2(\mathbb N)$, enough for separable $\mathcal X$. Separability is the standing assumption of Errata (i), p. 24.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 16, Lemma 3.9 (M¹(X) defined on p. 15); Errata (i), p. 24

import Mathlib
import Definitions.Def_DistCov_Indep_Setting

namespace DistCov.Indep

open MeasureTheory

theorem lemma_3_9 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (h : StrongNegType X) : ∃ ϕ : X → L2N, IsNegTypeEmbedding ϕ ∧ BaryInjM1 ϕ := by sorry

end DistCov.Indep

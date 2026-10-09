-- Prove2me | Theorems.Thm_DistCov_Indep_lemma_3_8
-- name    : DistCov.Indep.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:08.991986+00:00
-- url     : https://prove2.me/theorems/44aac2d2-c9d4-450f-acc3-39bd9b482821
-- title:
--   Lemma 3.8 (Errata (ix), p. 27) — embeddings witnessing strong negative type with β_{ϕ⊗ψ} injective on M^{1,1}(X × Y)
-- statement:
--   Let $\mathcal X$ and $\mathcal Y$ be separable metric spaces with their Borel $\sigma$-fields, both of strong negative type. Then there are embeddings $\phi:\mathcal X\to\ell^2(\mathbb N)$ and $\psi:\mathcal Y\to\ell^2(\mathbb N)$ (so $d(x,x')=\|\phi(x)-\phi(x')\|^2$ and $d(y,y')=\|\psi(y)-\psi(y')\|^2$) that witness strong negative type, i.e. $\beta_\phi$ and $\beta_\psi$ are injective on the probability measures with finite first moment, such that
--   $$\beta_{\phi\otimes\psi}\ \text{is injective on}\ M^{1,1}(\mathcal X\times\mathcal Y),$$
--   the finite signed measures $\theta$ on $\mathcal X\times\mathcal Y$ such that both marginals of $|\theta|$ have finite first moment. Here $\beta_{\phi\otimes\psi}(\theta)=\int\phi(x)\otimes\psi(y)\,d\theta(x,y)$ in the Hilbert tensor product $\ell^2\otimes\ell^2$.
--
--   This is the reformulation given in the Errata (ix), which repairs a gap in the original proof of Lemma 3.8 and incorporates Lemma 3.9. It is the injectivity that, combined with Proposition 3.7, turns $\operatorname{dcov}(\theta)=0$ into $\theta=\mu\times\nu$.
--
--   **Formalization Note** Injectivity on $M^{1,1}$ is stated through pairs of finite measures $m_1,m_2$ on $\mathcal X\times\mathcal Y$ whose marginals all have finite first moment (equivalent via the Jordan decomposition: the marginals of $|\theta|$ have finite first moment iff those of $\theta^+$ and $\theta^-$ do). "Witness strong negative type" is the barycenter injectivity of Proposition 3.1. The errata embed into $H\oplus\mathbb R$; for separable spaces this is a separable Hilbert space, so the target is fixed to $\ell^2(\mathbb N)$. Separability is the standing assumption of Errata (i), p. 24.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 27, Errata (ix), Lemma 3.8 (replacing the original Lemma 3.8, p. 15; M^{1,1} defined on p. 15); Errata (i), p. 24

import Mathlib
import Definitions.Def_DistCov_Indep_Setting

namespace DistCov.Indep

open MeasureTheory

theorem lemma_3_8 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (hX : StrongNegType X) (hY : StrongNegType Y) :
    ∃ ϕ : X → L2N, ∃ ψ : Y → L2N, IsNegTypeEmbedding ϕ ∧ IsNegTypeEmbedding ψ ∧
      BaryInjProb ϕ ∧ BaryInjProb ψ ∧ TensorBaryInjM11 ϕ ψ := by sorry

end DistCov.Indep

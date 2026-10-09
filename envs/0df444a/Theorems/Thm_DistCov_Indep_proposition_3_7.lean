-- Prove2me | Theorems.Thm_DistCov_Indep_proposition_3_7
-- name    : DistCov.Indep.proposition_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:31.669195+00:00
-- url     : https://prove2.me/theorems/3a0437f0-b0ec-44a4-9977-8dae04b9bdf3
-- title:
--   Proposition 3.7 — dcov(θ) = 4‖β_{ϕ⊗ψ}(θ − µ × ν)‖²
-- statement:
--   Let $\mathcal X$ and $\mathcal Y$ be separable metric spaces with their Borel $\sigma$-fields, of negative type as witnessed by embeddings $\phi:\mathcal X\to H$ and $\psi:\mathcal Y\to K$ into real Hilbert spaces. Let $\theta$ be a probability measure on $\mathcal X\times\mathcal Y$ whose marginals $\mu$ and $\nu$ have finite first moments. Then $\theta\circ(\phi\otimes\psi)^{-1}$ has finite first moment, i.e. the tensor embedding $(x,y)\mapsto\phi(x)\otimes\psi(y)\in H\otimes K$ is $\theta$-integrable, so that $\beta_{\phi\otimes\psi}(\theta)$ is defined, and
--   $$\operatorname{dcov}(\theta)=4\,\big\|\beta_{\phi\otimes\psi}(\theta-\mu\times\nu)\big\|^2 .$$
--
--   The proposition identifies distance covariance with the squared distance, in the Hilbert tensor product, between the barycenters of $\theta$ and of the product of its marginals. In particular $\operatorname{dcov}(\theta)\ge0$ on spaces of negative type, and $\operatorname{dcov}(\theta)=0$ exactly when these two barycenters coincide.
--
--   **Formalization Note** $H\otimes K$ is the completion of the algebraic tensor product with the inner product $\langle h_1\otimes k_1,h_2\otimes k_2\rangle=\langle h_1,h_2\rangle\langle k_1,k_2\rangle$. The paper uses one space $H$ for both factors; allowing two spaces is a harmless generalization of a universally quantified statement. $\beta_{\phi\otimes\psi}(\theta-\mu\times\nu)$ is written $\beta_{\phi\otimes\psi}(\theta)-\beta_{\phi\otimes\psi}(\mu\times\nu)$ by linearity. "Finite first moment of $\theta\circ(\phi\otimes\psi)^{-1}$" is stated as Bochner integrability of $\phi\otimes\psi$ with respect to $\theta$. Separability is the standing assumption of Errata (i), p. 24.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 14, Proposition 3.7 (tensor embedding defined on p. 13); Errata (i), p. 24

import Mathlib
import Definitions.Def_DistCov_Indep_Setting

namespace DistCov.Indep

open MeasureTheory

theorem proposition_3_7 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (ϕ : X → H) (ψ : Y → K) (hϕ : IsNegTypeEmbedding ϕ) (hψ : IsNegTypeEmbedding ψ)
    (θ : Measure (X × Y)) [IsProbabilityMeasure θ]
    (hμ : FiniteFirstMoment (θ.map Prod.fst)) (hν : FiniteFirstMoment (θ.map Prod.snd)) :
    Integrable (tensorEmb ϕ ψ) θ ∧
    dcov θ = 4 * ‖bary (tensorEmb ϕ ψ) θ
      - bary (tensorEmb ϕ ψ) ((θ.map Prod.fst).prod (θ.map Prod.snd))‖ ^ 2 := by sorry

end DistCov.Indep

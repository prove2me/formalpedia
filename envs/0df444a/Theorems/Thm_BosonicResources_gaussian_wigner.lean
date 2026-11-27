-- Prove2me | Theorems.Thm_BosonicResources_gaussian_wigner
-- name    : BosonicResources.gaussian_wigner
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T05:45:02.926854+00:00
-- url     : https://prove2.me/theorems/401e0d8d-444b-490c-bde8-06c11a440f63
-- title:
--   The Wigner function of the Gaussian state $\rho(\mu,\Sigma)$ is the density of $\mathcal N(\mu,\Sigma)$
-- statement:
--   An $n$-mode bosonic system has quadrature operators $\hat r=(\hat x_1,\dots,\hat x_n,\hat p_1,\dots,\hat p_n)$. For $\mu\in\mathbb R^{2n}$ and a real $2n\times 2n$ matrix $\Sigma$, $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu$ and covariance matrix $\Sigma$, in the convention $\Sigma_{jk}=\tfrac12\operatorname{Tr}\big(\rho\,\{\hat r_j-\mu_j,\hat r_k-\mu_k\}\big)$, so that the vacuum has covariance $\tfrac12 I$. For a density operator $\rho$ with Fock matrix elements $\rho_{uv}=\langle u\rvert\rho\lvert v\rangle$ ($u,v\in\mathbb N^{n}$), the Wigner function at a phase-space point $r\in\mathbb R^{2n}$ is $W_\rho(r)=\sum_{u}\sum_{v}\rho_{uv}\,W_{\lvert u\rangle\langle v\rvert}(r)$, where $W_{\lvert u\rangle\langle v\rvert}$ is the Wigner function of the Fock matrix unit $\lvert u\rangle\langle v\rvert$.
--
--   Let $\rho=\rho(\mu,\Sigma)$ be an $n$-mode Gaussian state. Then for every $r\in\mathbb R^{2n}$
--
--   $$
--   W_\rho(r)=\frac{1}{(2\pi)^{n}\sqrt{\det\Sigma}}\exp\!\Big(-\tfrac12\,(r-\mu)^{T}\Sigma^{-1}(r-\mu)\Big),
--   $$
--
--   that is, the Wigner function of $\rho(\mu,\Sigma)$ is the probability density of the Gaussian distribution $\mathcal N(\mu,\Sigma)$ on $\mathbb R^{2n}$.
--
--   In the paper this is the definition of a Gaussian state ("a quantum state whose Wigner function is a Gaussian distribution"). The statement justifies identifying the Wigner distribution of $\rho(\mu,\Sigma)$ with $\mathcal N(\mu,\Sigma)$ in Theorem 1, Lemma 1 and Lemmas B.1 to B.3, and it ties the Wigner-function conventions behind the notion of classical measurement to the mean and covariance conventions of Gaussian states.
--
--   **Formalization Note** The published `BosonicLearn.IsGaussianState` defines Gaussian states through the characteristic function; this statement identifies that definition with the paper's (Gaussian Wigner function) and fixes the conventions of `fockWigner` against it. $W_\rho$ is the iterated series over the Fock basis, which converges for every density operator. The right-hand side is a real number embedded in the complex numbers, and no lower bound on $n$ is assumed.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, Sec. 2 (definition of Gaussian states and of the Wigner function)

import Mathlib
import Definitions.Def_BosonicLearn_IsGaussianState
import Definitions.Def_BosonicResources_fockWigner
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **The Wigner function of the Gaussian state `ρ(µ, Σ)` is the density of `N(µ, Σ)`.**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, §2: "A Gaussian state ρ is a quantum state whose Wigner function is a Gaussian distribution, i.e.,
W_ρ(r) = N(µ,Σ). They are completely determined by their mean and covariance, usually denoted by ρ(µ,Σ)."

For an `n`-mode Gaussian state `ρ = ρ(µ, Σ)` and every phase-space point `r ∈ ℝ²ⁿ`, the Wigner function
`W_ρ(r) = ∑_u ∑_v ρ_{uv} W_{|u⟩⟨v|}(r)` (with `W_{|u⟩⟨v|}` the Fock Wigner function `fockWigner u v`) equals

`(2π)^{-n} (det Σ)^{-1/2} exp(−½ (r − µ)ᵀ Σ⁻¹ (r − µ))`.

**Formalization Note.** The published `BosonicLearn.IsGaussianState` defines Gaussian states through the
characteristic function; this statement identifies that definition with the paper's (Gaussian Wigner function) and
fixes the conventions of `fockWigner` against it. `W_ρ` is the iterated series, which converges for every density
operator. -/
theorem gaussian_wigner {n : ℕ} (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (hρ : IsGaussianState ρ μ S)
    (r : EuclideanSpace ℝ (Fin n ⊕ Fin n)) :
    ∑' u : Occupation (Fin n), ∑' v : Occupation (Fin n), ρ.coefficients u v * fockWigner u v r =
      ((1 / ((2 * Real.pi) ^ n * Real.sqrt S.det) *
        Real.exp (-(1 / 2) * ((WithLp.ofLp r - μ) ⬝ᵥ (S⁻¹ *ᵥ (WithLp.ofLp r - μ)))) : ℝ) : ℂ) := by sorry

end BosonicResources

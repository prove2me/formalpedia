-- Prove2me | Theorems.Thm_BosonicLearn_traceDist_gaussian_common_mean
-- name    : BosonicLearn.traceDist_gaussian_common_mean
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T07:04:39.385629+00:00
-- url     : https://prove2.me/theorems/69ea5a8d-7e7f-4259-8b91-2fec910d2093
-- title:
--   $\|\rho(\mu,\Sigma_1)-\rho(\mu,\Sigma_2)\|_1=\|\rho(\mu',\Sigma_1)-\rho(\mu',\Sigma_2)\|_1$: a common displacement does not change the trace distance
-- statement:
--   The trace distance between two Gaussian states with the same mean depends only on the two covariance matrices.
--
--   Let $\rho_1=\rho(\mu,\Sigma_1)$, $\rho_2=\rho(\mu,\Sigma_2)$, $\sigma_1=\rho(\mu',\Sigma_1)$, $\sigma_2=\rho(\mu',\Sigma_2)$ be $n$-mode Gaussian states. Then
--
--   $$
--   \tfrac12\|\rho_1-\rho_2\|_1=\tfrac12\|\sigma_1-\sigma_2\|_1 .
--   $$
--
--   Why it holds. A state is determined by its characteristic function, so $\rho_k=D\,\sigma_kD^\dagger$ for the displacement operator $D$ by $\mu-\mu'$, a unitary, and the trace norm is invariant under conjugation by a unitary.
--
--   Role. Theorem 7 bounds $\tfrac12\|\rho(0,\Sigma')-\rho(0,\bar\Sigma)\|_1$ for centred states. In the proof of Theorem 8 it is applied to $\rho(\hat\mu,\tilde\Sigma)$ and $\rho(\hat\mu,\Sigma)$ through this identity.
--
--   **Formalization Note** `IsGaussianState ρ μ S` is the mission's predicate for $\rho=\rho(\mu,\Sigma)$: the characteristic function of $\rho$ is $\exp(\mathrm i\xi\cdot\mu-\tfrac12\xi^\top\Sigma\xi)$, together with finite energy, symmetry of $\Sigma$ and the first and second moment identities; quadratures are in grouped order $(q_1,\dots,q_n,p_1,\dots,p_n)$ and the vacuum has $\Sigma=\tfrac12\mathbf 1$. States are `State (Occupation (Fin n))`, density operators on $\ell^2(\mathbb N^n)$. The four states are given through the predicate, so the statement also contains uniqueness of the Gaussian state with given moments (take $\mu'=\mu$ and $\Sigma_1=\Sigma_2$). `traceDist` is $\tfrac12\|\cdot\|_1$ with values in `ℝ≥0∞`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, p. 62 ("Since a common displacement is implemented by the same unitary on both states, trace distance is invariant under it", proof of Theorem 8)

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicLearn_IsGaussianState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open MeasureTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **The trace distance of two Gaussian states with a common mean does not depend on the mean.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §7.2, proof of Theorem 8, p. 62: "Since a common displacement is implemented by the same unitary on both
states, trace distance is invariant under it. Therefore ‖ρ(µ̂, Σ̃) − ρ(µ̂, Σ)‖₁ = ‖ρ(0, Σ̃) − ρ(0, Σ)‖₁."

For Gaussian states `ρ(µ, Σ₁)`, `ρ(µ, Σ₂)` and `ρ(µ′, Σ₁)`, `ρ(µ′, Σ₂)`,
`½‖ρ(µ, Σ₁) − ρ(µ, Σ₂)‖₁ = ½‖ρ(µ′, Σ₁) − ρ(µ′, Σ₂)‖₁`.

**Formalization Note.** The four states are given by their defining predicate; the statement includes that a
Gaussian state is determined by its mean and covariance (take `µ′ = µ`, `Σ₁ = Σ₂`). -/
theorem traceDist_gaussian_common_mean {n : ℕ} (ρ₁ ρ₂ σ₁ σ₂ : State (Occupation (Fin n)))
    (μ μ' : Fin n ⊕ Fin n → ℝ) (S₁ S₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (h₁ : IsGaussianState ρ₁ μ S₁) (h₂ : IsGaussianState ρ₂ μ S₂)
    (k₁ : IsGaussianState σ₁ μ' S₁) (k₂ : IsGaussianState σ₂ μ' S₂) :
    traceDist ρ₁.coefficients ρ₂.coefficients = traceDist σ₁.coefficients σ₂.coefficients := by sorry

end BosonicLearn

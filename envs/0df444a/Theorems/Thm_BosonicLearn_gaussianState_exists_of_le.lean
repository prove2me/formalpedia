-- Prove2me | Theorems.Thm_BosonicLearn_gaussianState_exists_of_le
-- name    : BosonicLearn.gaussianState_exists_of_le
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T07:03:51.312201+00:00
-- url     : https://prove2.me/theorems/2863fb98-73bc-4b56-bf49-f0e597831635
-- title:
--   If $\Sigma$ is a valid covariance matrix and $\Sigma'\succeq\Sigma$ then $\rho(\mu',\Sigma')$ exists for every $\mu'$
-- statement:
--   Enlarging the covariance of a Gaussian state, and displacing it, gives a Gaussian state.
--
--   Let $\rho(\mu,\Sigma)$ be an $n$-mode Gaussian state. Let $\Sigma'$ be a real $2n\times2n$ matrix with $\Sigma'-\Sigma$ positive semidefinite, and $\mu'\in\mathbb R^{2n}$. Then there is an $n$-mode Gaussian state with mean $\mu'$ and covariance matrix $\Sigma'$.
--
--   Why it holds. $\Sigma'+\tfrac{\mathrm i}2\Omega=(\Sigma+\tfrac{\mathrm i}2\Omega)+(\Sigma'-\Sigma)\succeq0$, so $\Sigma'$ is a valid covariance matrix. Concretely $\rho(\mu',\Sigma')=\int D_x\,\rho(\mu,\Sigma)\,D_x^\dagger\,\mathrm d\gamma(x)$ with $D_x$ the displacement operators and $\gamma$ the Gaussian measure on $\mathbb R^{2n}$ with mean $\mu'-\mu$ and covariance $\Sigma'-\Sigma$.
--
--   Role. In the proof of Theorem 8 this gives, on the good event where $\tilde\Sigma\succeq\Sigma$, the estimate $\rho(\hat\mu,\tilde\Sigma)$, the intermediate state $\rho(\hat\mu,\Sigma)$ and the centred states $\rho(0,\tilde\Sigma)$, $\rho(0,\Sigma)$ to which Theorem 7 applies.
--
--   **Formalization Note** `IsGaussianState ρ μ S` is the mission's predicate for $\rho=\rho(\mu,\Sigma)$: the characteristic function of $\rho$ is $\exp(\mathrm i\xi\cdot\mu-\tfrac12\xi^\top\Sigma\xi)$, together with finite energy, symmetry of $\Sigma$ and the first and second moment identities; quadratures are in grouped order $(q_1,\dots,q_n,p_1,\dots,p_n)$ and the vacuum has $\Sigma=\tfrac12\mathbf 1$. States are `State (Occupation (Fin n))`, density operators on $\ell^2(\mathbb N^n)$. The hypothesis is `Matrix.PosSemidef (S' − S)`, which contains the symmetry of `S' − S`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, p. 62 ("Σ̃ + (i/2)Ω = (Σ + (i/2)Ω) + (Σ̃ − Σ) ⪰ 0 … Thus Σ̃ is physical", proof of Theorem 8)

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_BosonicLearn_IsGaussianState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open MeasureTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Gaussian states exist above a valid covariance matrix, with any mean.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §7.2, proof of Theorem 8, p. 62: "Σ̃ + (i/2)Ω = (Σ + (i/2)Ω) + (Σ̃ − Σ) ⪰ 0, because Σ is a valid covariance
matrix and Σ̃ − Σ ⪰ 0. Thus Σ̃ is physical".

If `Σ` is the covariance matrix of some `n`-mode Gaussian state and `Σ′ ⪰ Σ` (real symmetric), then for every
`µ′ ∈ ℝ²ⁿ` there is a Gaussian state `ρ(µ′, Σ′)`.

**Formalization Note.** `Σ′ ⪰ Σ` is positive semidefiniteness of `Σ′ − Σ`. Physically `ρ(µ′, Σ′)` is obtained
from `ρ(µ, Σ)` by a displacement and classical Gaussian noise of covariance `Σ′ − Σ`. With `Σ′ = Σ` the statement
gives all displacements of a Gaussian state. -/
theorem gaussianState_exists_of_le {n : ℕ} (ρ : State (Occupation (Fin n))) (μ : Fin n ⊕ Fin n → ℝ)
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (h : IsGaussianState ρ μ S)
    (μ' : Fin n ⊕ Fin n → ℝ) (S' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (hS' : (S' - S).PosSemidef) :
    ∃ ρ' : State (Occupation (Fin n)), IsGaussianState ρ' μ' S' := by sorry

end BosonicLearn

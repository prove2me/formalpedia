-- Prove2me | Theorems.Thm_BosonicResources_passive_iff_williamson
-- name    : BosonicResources.passive_iff_williamson
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-27T05:47:13.963919+00:00
-- url     : https://prove2.me/theorems/9451314c-d0b2-571d-ba60-44d81160ee28
-- title:
--   Passive Gaussian states: zero mean and a Williamson form with an orthogonal symplectic matrix
-- statement:
--   Throughout, $\rho(\mu,\Sigma)$ denotes the $n$-mode Gaussian state with mean $\mu\in\mathbb R^{2n}$ and covariance matrix $\Sigma$, a real $2n\times 2n$ matrix; quadratures are ordered $(x_1,\dots,x_n,p_1,\dots,p_n)$ and the vacuum has covariance $\tfrac12 I$. Let $\Omega=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$; a real $2n\times2n$ matrix $K$ is *symplectic* if $K\Omega K^{T}=\Omega$ and *orthogonal* if $K^{T}K=I$.
--
--   For a density operator $\rho$ on the $n$-mode Fock space, the following two conditions are equivalent.
--
--   1. $\rho$ is a Gaussian state whose density operator is block diagonal in the total photon number: $\langle u\rvert\rho\lvert v\rangle=0$ for all Fock states $\lvert u\rangle,\lvert v\rangle$ with $\sum_j u_j\neq\sum_j v_j$.
--   2. $\rho$ is a zero-mean Gaussian state $\rho(0,\Sigma)$ whose covariance matrix has a Williamson decomposition in which the symplectic matrix is also orthogonal: there are a real $2n\times 2n$ matrix $K$ that is both symplectic and orthogonal, and real numbers $d_1,\dots,d_n>0$, such that
--
--   $$
--   \Sigma=K\,D\,K^{T},\qquad D=\operatorname{diag}(d_1,\dots,d_n,d_1,\dots,d_n).
--   $$
--
--   Condition 2 is the definition of a passive Gaussian state in the present paper (a thermal state acted on by a passive Gaussian unitary); condition 1 is the definition of passivity under which all statements of this mission are written. The equivalence therefore certifies that the theorems about passive states, in particular Theorem 2, Theorem S6 and Theorem S9, concern the same class of states as the paper.
--
--   **Formalization Note** This identifies the definition of passivity used in the mission (the published `BosonicLearn.IsPassive`, taken from the companion paper arXiv:2609.26705, §1.1) with the definition of the present paper. The Williamson decomposition is the published predicate `AgnGaussTomo.IsWilliamson` ($K$ in Mathlib's `Matrix.symplecticGroup`, i.e. $KJK^{T}=J$ with $J=\begin{pmatrix}0&-I\\I&0\end{pmatrix}=-\Omega$, the same group as for $\Omega$; $d_j>0$, the symplectic eigenvalues; grouped quadrature order). Orthogonality of $K$ is membership in `Matrix.orthogonalGroup`. The positivity $d_j>0$ is part of the statement; no ordering of the $d_j$ and no lower bound on $n$ are imposed.
-- source:
--   Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, What resources are needed for optimal learning of bosonic Gaussian states?, https://arxiv.org/abs/2603.18136, App. A (definition of passive Gaussian states; Williamson form); App. D.2, Eq. (S131)

import Mathlib
import Definitions.Def_BosonicLearn_IsPassive
import Definitions.Def_AgnGaussTomo_IsWilliamson
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open BosonicLearn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicResources

/-- **Passive Gaussian states: zero mean and a Williamson form with an orthogonal symplectic matrix.**
Chen, Mele, Fanizza, Li, Mann, Huang, Chen, Preskill, *What resources are needed for optimal learning of bosonic
Gaussian states?*, arXiv:2603.18136, App. A: "A Gaussian state is called passive if it has zero mean and its covariance matrix can be written in
Williamson form as V = K D Kᵀ, where K is symplectic orthogonal. Equivalently, a passive Gaussian state is a state
obtained by applying a passive Gaussian unitary … to a thermal state"; App. D.2, Eq. (S131): "a passive Gaussian state
is a Gaussian state with a vanishing first moment and a covariance matrix Σ that admits a Williamson decomposition
Σ = O D Oᵀ via a symplectic matrix O that is also orthogonal"; Williamson form (App. A):
`D = diag(ν₁,…,νₙ,ν₁,…,νₙ)`.

For a density operator `ρ` on the `n`-mode Fock space, the following are equivalent:
1. `ρ` is passive in the sense of the published `BosonicLearn.IsPassive`: a Gaussian state whose Fock matrix is block
   diagonal in the total photon number;
2. `ρ` is a zero-mean Gaussian state `ρ(0, Σ)` whose covariance has a Williamson decomposition `Σ = K D Kᵀ`,
   `D = diag(d₁,…,dₙ,d₁,…,dₙ)` with all `d_j > 0` and `K` symplectic, in which `K` is also orthogonal.

**Formalization Note.** This identifies the definition of passivity used in the mission (taken from the companion
paper arXiv:2609.26705, §1.1) with the definition of the present paper. The Williamson decomposition is the published
predicate `AgnGaussTomo.IsWilliamson` (`K ∈ Matrix.symplecticGroup`, i.e. `K J Kᵀ = J` with `J = [[0, −I],[I, 0]] = −Ω`,
the same group as for `Ω`; `d_j > 0`, the symplectic eigenvalues; grouped quadrature order). -/
theorem passive_iff_williamson {n : ℕ} (ρ : State (Occupation (Fin n))) :
    IsPassive ρ ↔
      ∃ (S K : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (d : Fin n → ℝ),
        IsGaussianState ρ 0 S ∧ AgnGaussTomo.IsWilliamson S K d ∧
          K ∈ Matrix.orthogonalGroup (Fin n ⊕ Fin n) ℝ := by sorry

end BosonicResources

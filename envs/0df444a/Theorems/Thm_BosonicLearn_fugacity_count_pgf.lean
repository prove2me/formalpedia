-- Prove2me | Theorems.Thm_BosonicLearn_fugacity_count_pgf
-- name    : BosonicLearn.fugacity_count_pgf
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T19:58:21.681829+00:00
-- url     : https://prove2.me/theorems/776e82db-e4dc-4ed7-9ce3-cd547bbbe1cf
-- title:
--   Photon count of a passive Gaussian state on a subspace of modes: $\mathbb E\,z^{K}=\det(1+(1-z)B)^{-1}$
-- statement:
--   The probability generating function of the photon number in a subspace of modes, for a passive Gaussian state.
--
--   Let $R$ be a fugacity matrix (positive semidefinite with $1-R$ positive definite), $N=R(1-R)^{-1}$ its photon occupation matrix, $U$ a unitary $n\times n$ matrix and $A$ a set of modes. Apply the passive unitary of $U$ to $\rho_R=\det(1-R)\Gamma(R)$ (this gives $\rho_{URU^\dagger}$) and count the photons in the modes of $A$: outcome $k$ has probability $p_k=\sum_{w:\sum_{i\in A}w_i=k}\langle w|\rho_{URU^\dagger}|w\rangle\ge0$. Then for $0\le z\le1$
--
--   $$
--   \sum_{k\ge0}p_k\,z^k=\frac1{\det\big(1+(1-z)B\big)},\qquad B=P_A\,UNU^\dagger\,P_A ,
--   $$
--
--   where $P_A$ is the coordinate projection on the modes of $A$; the determinant is real and positive.
--
--   Consequence. If $\lambda_i$ are the eigenvalues of $B$, the right-hand side is $\prod_i\frac1{1+\lambda_i(1-z)}$, the generating function of a sum of independent geometric variables with means $\lambda_i$ (Eqs. (135)–(136) of the paper).
--
--   Checked numerically for random $2$-mode $R$, $U$, all $A$ and several $z$.
--
--   **Formalization Note** $B$ is kept as an $n\times n$ matrix supported on $A\times A$ (the paper's $B_X$ padded by zeros), which has the same determinant $\det(1+(1-z)B)$. The statement is a conjunction: $p_k\ge0$ for all $k$; and for each $z\in[0,1]$, positivity of the real part of the determinant and `HasSum`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §5.7 (Delayed proof for Lemma 12), proof of Lemma 12, Eqs. (135)–(136)

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped Matrix ComplexOrder

namespace BosonicLearn

/-- **Photon counting on a subspace of modes: probability generating function.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §5.7, proof of Lemma 12, Eqs. (135)–(136): "We now measure the total photon number in the mode subspace ran Π₊ … The reduced
state on these m modes is again a passive Gaussian state, and its photon occupation matrix is B_X … E z^{K_X} =
det(I + (1 − z)B_X)^{−1}."

Let `R` be positive semidefinite with `1 − R` positive definite, `U` a unitary matrix and `A` a set of modes. Rotate
the passive Gaussian state `ρ_R = det(1 − R)Γ(R)` by the passive unitary of `U` (this gives `ρ_{URU†}`) and count the
photons in the modes of `A`: the outcome `k` has probability `p_k = ∑_{w : ∑_{i∈A} w_i = k} ⟨w|ρ_{URU†}|w⟩`. Then
`p_k ≥ 0` and, for `0 ≤ z ≤ 1`,

`∑ₖ p_k zᵏ = 1 / det(1 + (1 − z) B)`,  `B = P_A U N U† P_A`,  `N = R(1 − R)⁻¹`,

where `P_A` is the coordinate projection onto the modes of `A`; the determinant is a positive real number.

**Formalization Note.** `B` is kept as an `n × n` matrix supported on `A × A` (the paper's `B_X` padded by zeros), so
`det(1 + (1 − z)B)` is the determinant of the paper. -/
theorem fugacity_count_pgf {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) (A : Finset (Fin n)) :
    (∀ k : ℕ, 0 ≤ ∑' w : Occupation (Fin n),
        if ∑ i ∈ A, w i = k then (fugacityCoeff (U * R * Uᴴ) w w).re else 0) ∧
    ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      0 < (1 + ((1 - z : ℝ) : ℂ) • (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) *
          (U * (R * (1 - R)⁻¹) * Uᴴ) * Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0))).det.re ∧
      HasSum (fun k : ℕ => (∑' w : Occupation (Fin n),
            if ∑ i ∈ A, w i = k then (fugacityCoeff (U * R * Uᴴ) w w).re else 0) * z ^ k)
        ((1 + ((1 - z : ℝ) : ℂ) • (Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) *
          (U * (R * (1 - R)⁻¹) * Uᴴ) *
          Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0))).det.re)⁻¹ := by sorry

end BosonicLearn

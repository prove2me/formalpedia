-- Prove2me | Theorems.Thm_BoundEntPPT_exists_negative_expectation_partialTranspose
-- name    : BoundEntPPT.exists_negative_expectation_partialTranspose
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:25:10.251927+00:00
-- url     : https://prove2.me/theorems/b91cb39a-f155-448a-82ee-209077f78f43
-- title:
--   p.2, Eq. (10) — a negative expectation $\langle\psi|(\varrho^{\otimes N})^{T_B}|\psi\rangle<0$
-- statement:
--   Let $X$ be a Hermitian operator on $\mathcal H_A\otimes\mathcal H_B$ (in the paper $X=\varrho^{\otimes N}$) and let $P_A$, $P_B$ be orthogonal projectors (Hermitian idempotents) on $\mathcal H_A$, $\mathcal H_B$. If the partial transpose of $\varrho'=(P_A\otimes P_B)X(P_A\otimes P_B)$ is not positive semidefinite, then $\varrho'^{T_B}$ has an eigenvector $\psi\neq0$ for a negative eigenvalue, and **every** such eigenvector $\psi$ satisfies
--
--   $$
--   \langle\psi|\,X^{T_B}\,|\psi\rangle<0. \tag{10}
--   $$
--
--   Thus $X$ itself violates the partial transposition criterion. In the paper, $X=\varrho^{\otimes N}$ and $\psi$ is the eigenvector of $\varrho'^{T_B}$ for its negative eigenvalue, lying in the subspace on which $\varrho'^{T_B}$ and $(\varrho^{\otimes N})^{T_B}$ have the same matrix elements.
--
--   **Formalization Note** The partial transpose is the published `Information100.P04.gamma` in the computational product basis; $\langle\psi|Y|\psi\rangle$ is `star ψ ⬝ᵥ (Y *ᵥ ψ)`, of which the real part is taken (it is real for Hermitian $Y$). The paper's intermediate remark that $\psi$ lies in $\mathcal H_{2q}$ is a step of the proof and is not stated: in the computational basis a negative eigenvector of $\varrho'^{T_B}$ lies in the range of $P_A\otimes P_B^T$ (footnote [20]), not of $P_A\otimes P_B$.
--
--   Differences from the source:
--   - generalization: two-dimensional projectors P_A, P_B → any Hermitian idempotents P_A, P_B (no rank condition); reason: the step does not use the rank; it specializes to rank 2
--   - generalization: X = ϱ^{⊗N} for a state ϱ → any Hermitian X on any finite I × J; reason: the step uses only that X is Hermitian; it specializes at X = copies ρ N
--   - encoding: ϱ′^{T_B} has a negative eigenvalue → ¬ (gamma ϱ′).PosSemidef; reason: equivalent for the Hermitian ϱ′^{T_B}; taken in the computational product basis, whose choice does not change eigenvalues (p.2)
--   - encoding: ⟨ψ|(ϱ^{⊗N})^{T_B}|ψ⟩ < 0 → (star ψ ⬝ᵥ (gamma X *ᵥ ψ)).re < 0; reason: the expectation of a Hermitian matrix is real
--   - encoding: ψ, the eigenvector of the negative eigenvalue, belongs to the subspace H_{2q} → not stated; the conclusion is the existence of a negative eigenvector ψ of gamma ϱ′ and Eq. (10) for every such ψ; reason: membership in H_{2q} is a step of the proof that holds in the paper's adapted basis; in the computational basis the eigenvector lies in the range of P_A ⊗ P_Bᵀ instead
-- source:
--   M. Horodecki, P. Horodecki, R. Horodecki, Mixed-state entanglement and distillation: is there a "bound" entanglement in nature?, arXiv:quant-ph/9801069v1, p.2, Eq. (10)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
open scoped Matrix ComplexOrder

namespace BoundEntPPT

/-- M. Horodecki, P. Horodecki, R. Horodecki, *Mixed-state entanglement and distillation: is there
a "bound" entanglement in nature?*, arXiv:quant-ph/9801069v1, p.2, Eq. (10): "Now let ψ be the eigenvector corresponding to the eigenvalue. As
the vector belongs to the subspace H_{2q} it follows that the matrix elements ⟨ψ|ϱ′^{T_B}|ψ⟩ and
⟨ψ|(ϱ^{⊗N})^{T_B}|ψ⟩ are equal. Hence we obtain ⟨ψ|(ϱ^{⊗N})^{T_B}|ψ⟩ < 0. (10) Thus the state
ϱ^{⊗N} violates the partial transposition criterion."

Let `X` be Hermitian on `I × J`, `P_A`, `P_B` Hermitian idempotents and
`ϱ′ = (P_A ⊗ P_B) X (P_A ⊗ P_B)`. If `ϱ′^{T_B}` is not positive semidefinite, then it has an
eigenvector `ψ ≠ 0` for a negative eigenvalue, and every such eigenvector `ψ` satisfies
`⟨ψ|X^{T_B}|ψ⟩ < 0` (Eq. (10)); hence `X^{T_B}` is not positive semidefinite.

**Formalization Note.** `T_B` is the published `Information100.P04.gamma` (computational
product basis); `⟨ψ|Y|ψ⟩` is `star ψ ⬝ᵥ (Y *ᵥ ψ)`, real for Hermitian `Y`, of which the real
part is taken. The rank-2 condition of the paper's projectors is not needed and is dropped (a
generalization). The paper's "the vector belongs to the subspace H_{2q}" is a step of the proof
and is not stated: in the computational basis a negative eigenvector of `ϱ′^{T_B}` lies in the
range of `P_A ⊗ P_Bᵀ` (footnote [20]), not of `P_A ⊗ P_B`. -/
theorem exists_negative_expectation_partialTranspose {I J : Type*} [Fintype I] [Fintype J]
    (X : Matrix (I × J) (I × J) ℂ) (hX : X.IsHermitian)
    (PA : Matrix I I ℂ) (PB : Matrix J J ℂ)
    (hPA : PA.IsHermitian ∧ PA * PA = PA) (hPB : PB.IsHermitian ∧ PB * PB = PB)
    (h : ¬ (QAlgorithms.Papers.Independent.Information100.P04.gamma
      (Matrix.kronecker PA PB * X * Matrix.kronecker PA PB)).PosSemidef) :
    (∃ ψ : I × J → ℂ, ∃ μ : ℝ, ψ ≠ 0 ∧ μ < 0 ∧
      QAlgorithms.Papers.Independent.Information100.P04.gamma
        (Matrix.kronecker PA PB * X * Matrix.kronecker PA PB) *ᵥ ψ = (μ : ℂ) • ψ) ∧
    ∀ ψ : I × J → ℂ, ∀ μ : ℝ, ψ ≠ 0 → μ < 0 →
      QAlgorithms.Papers.Independent.Information100.P04.gamma
        (Matrix.kronecker PA PB * X * Matrix.kronecker PA PB) *ᵥ ψ = (μ : ℂ) • ψ →
      (dotProduct (star ψ)
        (QAlgorithms.Papers.Independent.Information100.P04.gamma X *ᵥ ψ)).re < 0 := by sorry

end BoundEntPPT

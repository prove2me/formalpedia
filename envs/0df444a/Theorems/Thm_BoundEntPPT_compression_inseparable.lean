-- Prove2me | Theorems.Thm_BoundEntPPT_compression_inseparable
-- name    : BoundEntPPT.compression_inseparable
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:25:01.925852+00:00
-- url     : https://prove2.me/theorems/5342e6a7-a3ac-4b8c-9654-02c52034d412
-- title:
--   p.2, Eqs. (7)–(9) — compressing $\varrho^{\otimes N}$ to the two-dimensional local supports keeps it inseparable
-- statement:
--   Let $X\succeq0$ be an operator on $\mathcal H_A\otimes\mathcal H_B$ (in the paper $X=\varrho^{\otimes N}$), and let $A:\mathcal H_A\to\mathbb C^2$, $B:\mathcal H_B\to\mathbb C^2$ be operators, written as in Eq. (7)
--
--   $$
--   A=|0\rangle\langle\psi_A|+|1\rangle\langle\phi_A|,\qquad B=|0\rangle\langle\psi_B|+|1\rangle\langle\phi_B| .
--   $$
--
--   Suppose $(A\otimes B)X(A\otimes B)^\dagger$ is not separable. Then there are **two-dimensional** orthogonal projectors $P_A$ on $\mathcal H_A$ and $P_B$ on $\mathcal H_B$ whose ranges contain $\psi_A,\phi_A$ and $\psi_B,\phi_B$ respectively (equivalently $AP_A=A$ and $BP_B=B$), such that Eq. (8) holds,
--
--   $$
--   (A\otimes B)X(A\otimes B)^\dagger=(A\otimes B)\big((P_A\otimes P_B)X(P_A\otimes P_B)\big)(A\otimes B)^\dagger,
--   $$
--
--   and the compressed operator of Eq. (9)
--
--   $$
--   \varrho'=(P_A\otimes P_B)\,X\,(P_A\otimes P_B)
--   $$
--
--   is not separable.
--
--   This step localizes the entanglement of a distilled pair to a $2\times2$-dimensional subspace of the $N$-copy system, where the two-qubit separability criterion can be applied.
--
--   **Formalization Note** A two-dimensional projector is a Hermitian idempotent matrix of rank exactly $2$. With $P_A$ Hermitian, $AP_A=A$ says that $P_A$ fixes $\psi_A,\phi_A$ (the columns of $A^\dagger$), so $P_A$ is the projector onto $\operatorname{span}\{\psi_A,\phi_A\}$ of the text. The hypothesis $X\succeq0$ is the paper's ($X=\varrho^{\otimes N}$) and is needed: it forces $\psi_A,\phi_A$ to be linearly independent, since a rank-one $A$ gives a separable output. Separability is the published cone `QAlgorithms.Entanglement.IsSeparablePositive`.
--
--   Differences from the source:
--   - generalization: X = ϱ^{⊗N} for a state ϱ → any positive semidefinite X on any finite I × J; reason: the step uses only X ⪰ 0; it specializes at X = copies ρ N
--   - encoding: two-dimensional projectors P_A, P_B → P Hermitian, P * P = P and P.rank = 2; reason: the definition of a rank-2 orthogonal projector
--   - encoding: P_A, P_B project onto span{ψ_A, φ_A}, span{ψ_B, φ_B} → ∃ P_A, P_B two-dimensional projectors with A * P_A = A and B * P_B = B; reason: for Hermitian P, A P = A says P fixes the columns ψ_A, φ_A of A†; with rank 2 this is the projector onto their span (they are independent under the hypotheses)
--   - encoding: separable (Eq. (2)) for unnormalized operators → QAlgorithms.Entanglement.IsSeparablePositive (finite sums Σ w_j A_j ⊗ B_j, w_j ≥ 0, A_j, B_j density matrices); reason: p.2 drops Σ p_i = 1 for unnormalized states; finite sums suffice in finite dimension (Carathéodory)
-- source:
--   M. Horodecki, P. Horodecki, R. Horodecki, Mixed-state entanglement and distillation: is there a "bound" entanglement in nature?, arXiv:quant-ph/9801069v1, p.2, Eqs. (7)–(9)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
open scoped Matrix ComplexOrder

namespace BoundEntPPT

/-- M. Horodecki, P. Horodecki, R. Horodecki, *Mixed-state entanglement and distillation: is there
a "bound" entanglement in nature?*, arXiv:quant-ph/9801069v1, p.2, Eqs. (7)–(9): "Note that the operators A_{i₀} and B_{i₀} act into
two-dimensional space C², hence they can be written in the form A_{i₀} = |0⟩⟨ψ_A| + |1⟩⟨φ_A|,
B_{i₀} = |0⟩⟨ψ_B| + |1⟩⟨φ_B|, (7) … Let us now consider two-dimensional projectors P_A and P_B
which project onto the spaces spanned by ψ_A, φ_A and ψ_B, φ_B respectively. Then we have
ϱ_{i₀} = A_{i₀} ⊗ B_{i₀} (P_A ⊗ P_B ϱ^{⊗N} P_A ⊗ P_B) A_{i₀}† ⊗ B_{i₀}†. (8) Now, since a product
action cannot convert separable state into inseparable one, we obtain that also the state
ϱ′ = P_A ⊗ P_B ϱ^{⊗N} P_A ⊗ P_B (9) is inseparable."

Let `X ⪰ 0` on `I × J` (the paper's `ϱ^{⊗N}`) and `A : I → C²`, `B : J → C²` with
`(A ⊗ B) X (A ⊗ B)†` not separable. Then there are two-dimensional orthogonal projectors `P_A`,
`P_B` (Hermitian, idempotent, rank 2) onto subspaces containing the vectors `ψ_A, φ_A`
(resp. `ψ_B, φ_B`) of (7), i.e. `A P_A = A`, `B P_B = B`, such that Eq. (8) holds and the
compression `ϱ′ = (P_A ⊗ P_B) X (P_A ⊗ P_B)` of Eq. (9) is not separable.

**Formalization Note.** `A P_A = A` with `P_A` Hermitian says that `P_A` fixes the columns of
`A†`, which are `ψ_A, φ_A`; with rank exactly 2 this makes `P_A` the projector onto
`span{ψ_A, φ_A}` of the text. The hypothesis `X ⪰ 0` is the paper's (`X = ϱ^{⊗N}`): it is what
forces `ψ_A, φ_A` (and `ψ_B, φ_B`) to be linearly independent, since a rank-one `A` gives a
product, hence separable, output. Separability is the published cone
`Entanglement.IsSeparablePositive`; `ᴴ` is the conjugate transpose. -/
theorem compression_inseparable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (X : Matrix (I × J) (I × J) ℂ) (hX : X.PosSemidef)
    (A : Matrix (Fin 2) I ℂ) (B : Matrix (Fin 2) J ℂ)
    (h : ¬ QAlgorithms.Entanglement.IsSeparablePositive
      (Matrix.kronecker A B * X * (Matrix.kronecker A B)ᴴ)) :
    ∃ PA : Matrix I I ℂ, ∃ PB : Matrix J J ℂ,
      (PA.IsHermitian ∧ PA * PA = PA ∧ PA.rank = 2) ∧
      (PB.IsHermitian ∧ PB * PB = PB ∧ PB.rank = 2) ∧
      A * PA = A ∧ B * PB = B ∧
      Matrix.kronecker A B * X * (Matrix.kronecker A B)ᴴ =
        Matrix.kronecker A B * (Matrix.kronecker PA PB * X * Matrix.kronecker PA PB) *
          (Matrix.kronecker A B)ᴴ ∧
      ¬ QAlgorithms.Entanglement.IsSeparablePositive
        (Matrix.kronecker PA PB * X * Matrix.kronecker PA PB) := by sorry

end BoundEntPPT

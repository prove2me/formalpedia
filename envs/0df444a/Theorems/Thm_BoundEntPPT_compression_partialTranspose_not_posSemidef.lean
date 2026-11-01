-- Prove2me | Theorems.Thm_BoundEntPPT_compression_partialTranspose_not_posSemidef
-- name    : BoundEntPPT.compression_partialTranspose_not_posSemidef
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:24:45.850993+00:00
-- url     : https://prove2.me/theorems/a0626a85-8432-4eb0-85fb-701e98d0a7d0
-- title:
--   p.2 (unnumbered, after Eq. (9)) — the inseparable compression $\varrho'$ violates the Peres criterion
-- statement:
--   Let $X\succeq0$ be an operator on $\mathcal H_A\otimes\mathcal H_B$ (in the paper $X=\varrho^{\otimes N}$) and let $P_A$, $P_B$ be two-dimensional orthogonal projectors on $\mathcal H_A$, $\mathcal H_B$. If
--
--   $$
--   \varrho'=(P_A\otimes P_B)\,X\,(P_A\otimes P_B)
--   $$
--
--   is not separable, then $\varrho'^{T_B}$ is not positive semidefinite, i.e. $\varrho'$ violates the Peres criterion ($\varrho'^{T_B}$ has a negative eigenvalue).
--
--   In the paper: $\varrho'$ is supported on a $2\times2$-dimensional product subspace, where it is a two-qubit operator $M_{2q}$; if $M_{2q}^{T_B}$ were positive, $M_{2q}$ and hence $\varrho'$ would be separable by the two-qubit result [15].
--
--   **Formalization Note** A two-dimensional projector is a Hermitian idempotent matrix of rank exactly $2$; the rank condition is essential (for $P_A=P_B=1$ the statement would claim that every entangled state violates the criterion, which is false). The partial transpose is the published `Information100.P04.gamma` in the computational product basis; "has a negative eigenvalue" is `¬ PosSemidef`, equivalent for the Hermitian $\varrho'^{T_B}$. Separability is the published cone `QAlgorithms.Entanglement.IsSeparablePositive`.
--
--   Differences from the source:
--   - generalization: X = ϱ^{⊗N} for a state ϱ → any positive semidefinite X on any finite I × J; reason: the argument uses only X ⪰ 0; it specializes at X = copies ρ N
--   - encoding: two-dimensional projectors P_A, P_B → P Hermitian, P * P = P and P.rank = 2; reason: the definition of a rank-2 orthogonal projector
--   - encoding: ϱ′^{T_B} has a negative eigenvalue → ¬ (gamma ϱ′).PosSemidef; reason: equivalent for the Hermitian ϱ′^{T_B}; taken in the computational product basis, whose choice does not change eigenvalues (p.2)
--   - encoding: separable (Eq. (2)) for unnormalized operators → QAlgorithms.Entanglement.IsSeparablePositive (finite sums Σ w_j A_j ⊗ B_j, w_j ≥ 0, A_j, B_j density matrices); reason: p.2 drops Σ p_i = 1 for unnormalized states; finite sums suffice in finite dimension (Carathéodory)
-- source:
--   M. Horodecki, P. Horodecki, R. Horodecki, Mixed-state entanglement and distillation: is there a "bound" entanglement in nature?, arXiv:quant-ph/9801069v1, p.2 (unnumbered, after Eq. (9): 'ϱ′^{T_B} must have a negative eigenvalue')

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
open scoped Matrix ComplexOrder

namespace BoundEntPPT

/-- M. Horodecki, P. Horodecki, R. Horodecki, *Mixed-state entanglement and distillation: is there
a "bound" entanglement in nature?*, arXiv:quant-ph/9801069v1, p.2 (unnumbered, after Eq. (9)): "If M_{2q} were positive after partial
transposition, then, due to the sufficiency of the partial transposition test for two-qubit case
[15], M_{2q} would represent a separable two-qubit state. Hence, if embedded into the whole space
H^{⊗N}, it would still remain separable. Consequently, the state ϱ′ would be separable, which is
the contradiction. Thus partial transposition of M_{2q} must be negative. Now, since M_{2q} is
formed by all nonzero elements of ϱ′, then we obtain that also the state ϱ′ must violate the
Peres criterion, i. e. ϱ′^{T_B} must have a negative eigenvalue."

Let `X ⪰ 0` on `I × J` and let `P_A`, `P_B` be two-dimensional orthogonal projectors (Hermitian,
idempotent, rank 2). If `ϱ′ = (P_A ⊗ P_B) X (P_A ⊗ P_B)` is not separable, then `ϱ′^{T_B}` is
not positive semidefinite.

**Formalization Note.** "Has a negative eigenvalue" is `¬ PosSemidef`, equivalent for the
Hermitian `ϱ′^{T_B}`. `T_B` is the published `Information100.P04.gamma` in the computational
product basis (the paper's `M_{2q}` lives in a basis adapted to `P_A`, `P_B`; p.2: "its
eigenvalues do not" depend on the basis). Rank exactly 2 is essential: for `P_A = P_B = 1` the
statement would assert that every inseparable state is NPT, which is false. Separability is the
published cone `Entanglement.IsSeparablePositive`. -/
theorem compression_partialTranspose_not_posSemidef {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (X : Matrix (I × J) (I × J) ℂ) (hX : X.PosSemidef)
    (PA : Matrix I I ℂ) (PB : Matrix J J ℂ)
    (hPA : PA.IsHermitian ∧ PA * PA = PA ∧ PA.rank = 2)
    (hPB : PB.IsHermitian ∧ PB * PB = PB ∧ PB.rank = 2)
    (h : ¬ QAlgorithms.Entanglement.IsSeparablePositive
      (Matrix.kronecker PA PB * X * Matrix.kronecker PA PB)) :
    ¬ (QAlgorithms.Papers.Independent.Information100.P04.gamma
      (Matrix.kronecker PA PB * X * Matrix.kronecker PA PB)).PosSemidef := by sorry

end BoundEntPPT

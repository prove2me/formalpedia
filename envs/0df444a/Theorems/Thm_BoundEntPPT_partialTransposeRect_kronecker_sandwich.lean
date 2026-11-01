-- Prove2me | Theorems.Thm_BoundEntPPT_partialTransposeRect_kronecker_sandwich
-- name    : BoundEntPPT.partialTransposeRect_kronecker_sandwich
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:00:52.436982+00:00
-- url     : https://prove2.me/theorems/cbc73f0f-2dbc-4cae-84c5-7e935338feb4
-- title:
--   p.4, footnote [20] — $(A\otimes B\,\varrho\,C\otimes D)^{T_B}=A\otimes D^T\,\varrho^{T_B}\,C\otimes B^T$
-- statement:
--   For arbitrary (not necessarily square) operators $A:\mathcal H_A\to\mathcal H_{A,1}$, $B:\mathcal H_B\to\mathcal H_{B,1}$, $C:\mathcal H_{A,2}\to\mathcal H_A$, $D:\mathcal H_{B,2}\to\mathcal H_B$ and every operator $\varrho$ on $\mathcal H_A\otimes\mathcal H_B$,
--
--   $$
--   \big((A\otimes B)\,\varrho\,(C\otimes D)\big)^{T_B}=(A\otimes D^T)\,\varrho^{T_B}\,(C\otimes B^T),
--   $$
--
--   where $T$ is the usual transposition (no complex conjugation) and $T_B$ the partial transposition on Bob's factor.
--
--   This identity is what makes partial transposition compatible with local operations: it underlies the passage from $\varrho'^{T_B}$ to $(\varrho^{\otimes N})^{T_B}$ in Eq. (10) and the generalization that every operation of form (4) preserves positivity of the partial transpose.
--
--   **Formalization Note** On the left the partial transpose of an operator between different spaces is `partialTransposeRect`; $\varrho^{T_B}$ is the published `Information100.P04.gamma`. Both are taken in the computational product basis.
--
--   Differences from the source:
--   - encoding: (·)^{T_B} of operators between possibly different spaces → partialTransposeRect for the left side, gamma for ϱ, in the computational basis; reason: the two agree on square matrices; footnote [20] is basis-free only up to this choice of product bases
-- source:
--   M. Horodecki, P. Horodecki, R. Horodecki, Mixed-state entanglement and distillation: is there a "bound" entanglement in nature?, arXiv:quant-ph/9801069v1, p.4, footnote [20]

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_BoundEntPPT_partialTransposeRect
open scoped Matrix ComplexOrder

namespace BoundEntPPT

/-- M. Horodecki, P. Horodecki, R. Horodecki, *Mixed-state entanglement and distillation: is there
a "bound" entanglement in nature?*, arXiv:quant-ph/9801069v1, p.4, footnote [20]: "It follows from the simple fact that for any operators
A, B, C, D we have (A ⊗ B ϱ C ⊗ D)^{T_B} = (A ⊗ D^T ϱ^{T_B} C ⊗ B^T) where T is usual
transposition."

For arbitrary (rectangular) `A : I → I₁`, `B : J → J₁`, `C : I₂ → I`, `D : J₂ → J` and
`X` on `I × J`,
`((A ⊗ B) X (C ⊗ D))^{T_B} = (A ⊗ Dᵀ) X^{T_B} (C ⊗ Bᵀ)`.

**Formalization Note.** `T_B` of the square `X` is the published `Information100.P04.gamma`
(Eq. (3)); `T_B` of the rectangular left-hand side is `partialTransposeRect`, which agrees with
`gamma` on square matrices. Both are taken in the computational product basis; `ᵀ` is the plain
transpose (no conjugation). -/
theorem partialTransposeRect_kronecker_sandwich {I J I₁ J₁ I₂ J₂ : Type*}
    [Fintype I] [Fintype J]
    (A : Matrix I₁ I ℂ) (B : Matrix J₁ J ℂ) (C : Matrix I I₂ ℂ) (D : Matrix J J₂ ℂ)
    (X : Matrix (I × J) (I × J) ℂ) :
    partialTransposeRect (Matrix.kronecker A B * X * Matrix.kronecker C D) =
      Matrix.kronecker A Dᵀ * QAlgorithms.Papers.Independent.Information100.P04.gamma X *
        Matrix.kronecker C Bᵀ := by sorry

end BoundEntPPT

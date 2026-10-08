-- Prove2me | Theorems.Thm_DiscreteConvex_MixedMatrices_card_le_rank_of_indep_transversal
-- name    : DiscreteConvex.MixedMatrices.card_le_rank_of_indep_transversal
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T13:35:15.776588+00:00
-- url     : https://prove2.me/theorems/5d8ca85a-fad4-4424-ad3f-24fec13e881f
-- title:
--   Independent transversals of the mixed-matrix family are bounded by the rank
-- statement:
--   Throughout, $R$ and $C$ are finite index sets, $K\subseteq F$ are fields (in Lean: `Algebra K F`), and for a matrix $M$ and subsets $I\subseteq R$, $J\subseteq C$ we write $M[I,J]$ for the submatrix with rows in $I$ and columns in $J$ and $\rho(I,J)=\operatorname{rank}Q[I,J]$, $\tau(I,J)=\operatorname{rank}T[I,J]$ for matrices $Q$ over $K$ and $T$ over $F$. A *mixed matrix* is $A=Q+T$ with $Q$ over $K$ and the nonzero entries of $T$ algebraically independent over $K$ (Murota, Ch. 12).
--
--   Let $A=Q+T$ be a mixed matrix. For each column $c\in C$ let $\mathcal A_c\subseteq F^R$ consist of the column $Q_c$ of $Q$ (viewed over $F$) together with the unit vectors $e_s$ for those rows $s$ with $T_{sc}\neq0$. If $(v_c)_{c\in J}$ is a linearly independent partial transversal of the family $(\mathcal A_c)_{c\in C}$, that is $v_c\in\mathcal A_c$ for $c\in J$, then
--
--   $$|J|\le\operatorname{rank}A .$$
--
--   **Formalization Note.** `hA : IsMixedMatrix A Q T` is the platform notion of a mixed matrix.
-- source:
--   Auxiliary lemma for Murota, Discrete Convex Analysis, SIAM 2003, Theorem 12.9 (p. 358), using Theorem 12.7 (p. 357); the route through Rado's theorem is not the book's

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedMatrix
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank

namespace DiscreteConvex.MixedMatrices

theorem card_le_rank_of_indep_transversal {R C K F : Type*} [Fintype R] [Fintype C] [Field K]
    [Field F] [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) (hA : IsMixedMatrix A Q T)
    (J : Finset C) (v : C → R → F)
    (hv : ∀ c ∈ J, v c ∈ ({fun r : R => algebraMap K F (Q r c)} ∪
      (fun s : R => (Pi.single s (1 : F) : R → F)) '' {s : R | T s c ≠ 0}))
    (hind : LinearIndepOn F v (J : Set C)) :
    J.card ≤ A.rank := by sorry

end DiscreteConvex.MixedMatrices

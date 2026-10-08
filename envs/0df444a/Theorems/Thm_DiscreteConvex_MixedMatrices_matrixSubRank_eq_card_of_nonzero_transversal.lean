-- Prove2me | Theorems.Thm_DiscreteConvex_MixedMatrices_matrixSubRank_eq_card_of_nonzero_transversal
-- name    : DiscreteConvex.MixedMatrices.matrixSubRank_eq_card_of_nonzero_transversal
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T13:35:01.762772+00:00
-- url     : https://prove2.me/theorems/139416fc-593c-4ffc-8c47-7f9f89ad7824
-- title:
--   A generic square block with nonzero diagonal is nonsingular
-- statement:
--   Throughout, $R$ and $C$ are finite index sets, $K\subseteq F$ are fields (in Lean: `Algebra K F`), and for a matrix $M$ and subsets $I\subseteq R$, $J\subseteq C$ we write $M[I,J]$ for the submatrix with rows in $I$ and columns in $J$ and $\rho(I,J)=\operatorname{rank}Q[I,J]$, $\tau(I,J)=\operatorname{rank}T[I,J]$ for matrices $Q$ over $K$ and $T$ over $F$. A *mixed matrix* is $A=Q+T$ with $Q$ over $K$ and the nonzero entries of $T$ algebraically independent over $K$ (Murota, Ch. 12).
--
--   Let $T$ be a matrix over $F$ whose nonzero entries are algebraically independent over $K$. Let $J\subseteq C$ and let $\psi:C\to R$ be injective on $J$ with $T_{\psi(c),c}\neq0$ for every $c\in J$. Then the square submatrix $T[\psi(J),J]$ is nonsingular:
--
--   $$\operatorname{rank}T[\psi(J),J]=|J| .$$
--
--   **Formalization Note.** Algebraic independence is that of the family of nonzero entries, indexed by the positions $(i,j)$ with $T_{ij}\neq0$.
-- source:
--   Standard fact on generic matrices (a square matrix with algebraically independent nonzero entries and a nonzero diagonal is nonsingular); auxiliary lemma for Murota, Discrete Convex Analysis, SIAM 2003, Theorem 12.8 (p. 358); not stated in the book

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank

namespace DiscreteConvex.MixedMatrices

theorem matrixSubRank_eq_card_of_nonzero_transversal {R C K F : Type*} [Fintype R] [Fintype C]
    [Field K] [Field F] [Algebra K F] [DecidableEq R] [DecidableEq C] (T : Matrix R C F)
    (hT : AlgebraicIndependent K (fun e : {p : R × C // T p.1 p.2 ≠ 0} => T e.1.1 e.1.2))
    (J : Finset C) (ψ : C → R) (hψ : Set.InjOn ψ (J : Set C)) (hne : ∀ c ∈ J, T (ψ c) c ≠ 0) :
    MatrixSubRank T (J.image ψ) J = J.card := by sorry

end DiscreteConvex.MixedMatrices

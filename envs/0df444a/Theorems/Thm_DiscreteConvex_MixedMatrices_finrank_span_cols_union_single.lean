-- Prove2me | Theorems.Thm_DiscreteConvex_MixedMatrices_finrank_span_cols_union_single
-- name    : DiscreteConvex.MixedMatrices.finrank_span_cols_union_single
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T13:35:13.577997+00:00
-- url     : https://prove2.me/theorems/0333b452-0aa8-4e8c-9244-4b9ac30372e0
-- title:
--   Dimension of the span of columns together with unit vectors
-- statement:
--   Let $R,C$ be finite index sets, let $M$ be a matrix over a field $F$ with rows indexed by $R$ and columns by $C$, let $J\subseteq C$ and $N\subseteq R$. Consider in $F^R$ the columns $M_c$ for $c\in J$ together with the unit vectors $e_s$ for $s\in N$. Then
--
--   $$\dim_F\operatorname{span}\bigl(\{M_c:c\in J\}\cup\{e_s:s\in N\}\bigr)=|N|+\operatorname{rank}M[R\setminus N,J] .$$
--
--   **Formalization Note.** `Pi.single s 1` is the unit vector $e_s\in F^R$; `MatrixSubRank M Nᶜ J` is the platform definition of $\operatorname{rank}M[R\setminus N,J]$.
-- source:
--   Auxiliary lemma for Murota, Discrete Convex Analysis, SIAM 2003, Theorems 12.8-12.9 (p. 358); elementary linear algebra, not stated in the book

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank

namespace DiscreteConvex.MixedMatrices

theorem finrank_span_cols_union_single {R C F : Type*} [Fintype R] [Fintype C] [Field F]
    [DecidableEq R] (M : Matrix R C F) (J : Finset C) (N : Finset R) :
    Module.finrank F (Submodule.span F
      (((fun c : C => (fun r : R => M r c)) '' (J : Set C)) ∪
        ((fun s : R => (Pi.single s (1 : F) : R → F)) '' (N : Set R)))) =
      N.card + MatrixSubRank M Nᶜ J := by sorry

end DiscreteConvex.MixedMatrices

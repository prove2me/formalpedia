-- Prove2me | Theorems.Thm_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit
-- name    : Algebra.exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/be560c54-e2ca-555c-9f31-9d38019e2cd1
-- title:
--   Spreading out a finitely presented algebra over a directed colimit
-- statement:
--   Let $\iota$ be a non-empty directed preordered index type, let $G$ be a family of commutative rings $G_i$ indexed by $\iota$, and let $f_{ij} \colon G_i \to G_j$ (for $i \le j$) be ring homomorphisms forming a directed system, i.e. compatible with the order in the sense of `DirectedSystem`. Let $R$ be a commutative ring that is an algebra over each $G_i$, and assume that the structure maps $\mathrm{algebraMap}(G_i, R)$ exhibit $R$ as the direct limit of the system in the sense of the predicate [`IsDirectLimit`](def/Mathlib_Algebra_IsDirectLimit.html#L8): every element of $R$ is the image of some element of some $G_i$; whenever $x \in G_i$ and $y \in G_j$ have the same image in $R$, there is $k \ge i, j$ with $f_{ik}(x) = f_{jk}(y)$; and the maps $G_i \to R$ are compatible with the transition maps, $\mathrm{algebraMap}(G_j,R)\circ f_{ij} = \mathrm{algebraMap}(G_i,R)$. Let $A$ be a commutative $R$-algebra of finite presentation. The conclusion asserts the existence of an index $i$, a type $A_0$ in the same universe as the rings $G_i$, carrying a commutative ring structure and a $G_i$-algebra structure making it a $G_i$-algebra of finite presentation, together with an isomorphism of $R$-algebras $R \otimes_{G_i} A_0 \cong A$ (stated as non-emptiness of the type of such isomorphisms).
--
--   This is the affine case of Grothendieck's spreading-out theorem for finitely presented algebras over a filtered colimit of rings: a finitely presented algebra over the limit ring descends, up to base change, to a finitely presented algebra over one stage of the system. It is used in the scheme-theoretic descent statement [`AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation`](thm.html#AlgebraicGeometry.exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v w w'

theorem Algebra.exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (G : ι → Type v) [∀ i, CommRing (G i)] (f : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [∀ i, Algebra (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (A : Type w') [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] :
    ∃ (i : ι) (A₀ : Type v) (_ : CommRing A₀) (_ : Algebra (G i) A₀)
      (_ : Algebra.FinitePresentation (G i) A₀), Nonempty ((R ⊗[G i] A₀) ≃ₐ[R] A) := by sorry

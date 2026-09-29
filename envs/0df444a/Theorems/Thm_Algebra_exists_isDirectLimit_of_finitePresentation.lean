-- Prove2me | Theorems.Thm_Algebra_exists_isDirectLimit_of_finitePresentation
-- name    : Algebra.exists_isDirectLimit_of_finitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/9c50316b-59e3-5679-bba0-fabedb07202e
-- title:
--   Every algebra is a direct limit of finitely presented algebras
-- statement:
--   Let $R$ be a commutative ring and $A$ a commutative $R$-algebra, both carriers in the same universe. The theorem asserts the existence of: an index type $\iota$ in that universe, a preorder on $\iota$, a proof that $\iota$ is nonempty and a proof that $\iota$ is directed for $\le$ (any two indices have a common upper bound); a family of types $S_i$ ($i \in \iota$) in the same universe, together with commutative ring structures on each $S_i$ and $R$-algebra structures making each $S_i$ a finitely presented $R$-algebra; transition $R$-algebra maps $t_{ij} \colon S_i \to S_j$ for every pair $i \le j$; $R$-algebra maps $c_i \colon S_i \to A$; and a proof that the underlying functions of the $t_{ij}$ form a directed system (each $t_{ii}$ is the identity and $t_{jk} \circ t_{ij} = t_{ik}$ on elements for $i \le j \le k$). The conclusion is that the underlying functions of the $c_i$ exhibit $A$ as the direct limit of this system in the sense of [`IsDirectLimit`](def/Mathlib_Algebra_IsDirectLimit.html#L8): every $a \in A$ equals $c_i(x)$ for some $i$ and some $x \in S_i$; whenever $c_i(x) = c_j(y)$ there are $k$ with $i \le k$, $j \le k$ and $t_{ik}(x) = t_{jk}(y)$; and $c_j(t_{ij}(x)) = c_i(x)$ for all $i \le j$ and $x \in S_i$.
--
--   This is the standard fact that an arbitrary algebra over a commutative ring is the filtered colimit of its finitely presented subalgebras-with-relations, here phrased concretely with an explicit directed index type rather than categorically. It is used for the recognition criterion [`Algebra.FinitePresentation.of_forall_isDirectLimit_exists_comp_eq`](thm.html#Algebra.FinitePresentation.of_forall_isDirectLimit_exists_comp_eq) and, via spreading-out arguments, in the treatment of invertible modules and polarisations on schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_isDirectLimit_of_finitePresentation.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem Algebra.exists_isDirectLimit_of_finitePresentation
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : Nonempty ι) (_ : IsDirected ι (· ≤ ·))
      (S : ι → Type u) (_ : ∀ i, CommRing (S i)) (_ : ∀ i, Algebra R (S i))
      (_ : ∀ i, Algebra.FinitePresentation R (S i))
      (t : ∀ i j : ι, i ≤ j → (S i →ₐ[R] S j)) (c : ∀ i, S i →ₐ[R] A)
      (_ : DirectedSystem S fun i j h => ⇑(t i j h)),
      IsDirectLimit (fun i j h => ⇑(t i j h)) fun i => ⇑(c i) := by sorry

-- Prove2me | Theorems.Thm_Algebra_FinitePresentation_of_forall_isDirectLimit_exists_comp_eq
-- name    : Algebra.FinitePresentation.of_forall_isDirectLimit_exists_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/656d269d-f7b3-5a3f-b61b-f134bb3f00e3
-- title:
--   Finite presentation from factoring maps through directed colimits
-- statement:
--   Let $R$ be a commutative ring and $A$ a commutative $R$-algebra, both types in a fixed universe $u$. Assume the following factorisation property: for every nonempty preordered index type $\iota$ in universe $u$ that is directed upwards, every family $S : \iota \to \mathrm{Type}\,u$ of commutative $R$-algebras, every family of $R$-algebra maps $t_{ij} : S_i \to S_j$ indexed by $i \le j$ forming a directed system (compatible with composition and with identities), every commutative $R$-algebra $L$ together with $R$-algebra maps $c_i : S_i \to L$ exhibiting $L$ as the direct limit of the system in the sense that (i) every element of $L$ is $c_i(m_i)$ for some $i$ and $m_i \in S_i$, (ii) whenever $c_i(m_i) = c_j(m_j)$ there is $k \ge i, j$ with $t_{ik}(m_i) = t_{jk}(m_j)$, and (iii) $c_j \circ t_{ij} = c_i$ for all $i \le j$, and every $R$-algebra map $\psi : A \to L$, there exist an index $i$ and an $R$-algebra map $\varphi : A \to S_i$ with $c_i \circ \varphi = \psi$. Then $A$ is a finitely presented $R$-algebra. Only this surjectivity half of the statement that $\mathrm{Hom}_R(A, -)$ commutes with directed colimits is assumed.
--
--   This is the converse direction of the characterisation of algebras of finite presentation by the property that maps out of them factor through the stages of a directed colimit (EGA IV 8.14.2). It is used to deduce the corresponding schematic statement [`AlgebraicGeometry.locallyOfFinitePresentation_of_forall_directed_colimit`](thm.html#AlgebraicGeometry.locallyOfFinitePresentation_of_forall_directed_colimit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FinitePresentation_of_forall_isDirectLimit_exists_comp_eq.lean

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem Algebra.FinitePresentation.of_forall_isDirectLimit_exists_comp_eq
    {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (H : ∀ (ι : Type u) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
      (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
      (t : ∀ i j : ι, i ≤ j → (S i →ₐ[R] S j)) [DirectedSystem S fun i j h => ⇑(t i j h)]
      (L : Type u) [CommRing L] [Algebra R L] (c : ∀ i, S i →ₐ[R] L)
      [IsDirectLimit (fun i j h => ⇑(t i j h)) fun i => ⇑(c i)]
      (ψ : A →ₐ[R] L), ∃ (i : ι) (φ : A →ₐ[R] S i), (c i).comp φ = ψ) :
    Algebra.FinitePresentation R A := by sorry

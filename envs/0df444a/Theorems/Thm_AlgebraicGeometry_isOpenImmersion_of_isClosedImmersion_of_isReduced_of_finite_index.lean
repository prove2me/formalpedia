-- Prove2me | Theorems.Thm_AlgebraicGeometry_isOpenImmersion_of_isClosedImmersion_of_isReduced_of_finite_index
-- name    : AlgebraicGeometry.isOpenImmersion_of_isClosedImmersion_of_isReduced_of_finite_index
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/8644b604-ff74-5b75-b077-2e53b6966651
-- title:
--   Closed subgroup of finite index on points is open
-- statement:
--   Let $k$ be an algebraically closed field, and let $f : X \to \operatorname{Spec} k$ be a morphism of schemes that is locally of finite type, with $X$ reduced. Suppose $X$ carries a relative group law $L$ over $k$, i.e. for every scheme $T'$ and every $k$-structure morphism $t' : T' \to \operatorname{Spec} k$ a multiplication, unit and inversion on the set $\{\varphi : T' \to X \mid \varphi \circ f = t'\}$ of $k$-morphisms to $X$, satisfying associativity, the two unit laws and left inverses, and compatible with precomposition along $k$-morphisms $T'' \to T'$. Let $tT : T \to \operatorname{Spec} k$ be a second $k$-scheme and $\iota : T \to X$ a closed immersion with $\iota$ followed by $f$ equal to $tT$. Assume: (i) for all $k$-points $\tau, \tau'$ of $T$ (sections of $tT$ over the identity of $\operatorname{Spec} k$) there is a $k$-point $\tau''$ of $T$ with $L$-product of $\iota \circ \tau$ and $\iota \circ \tau'$ equal to $\iota \circ \tau''$; (ii) likewise the $L$-inverse of $\iota \circ \tau$ is of the form $\iota \circ \tau'$; and (iii) there is a finite set $S$ of $k$-points of $X$ such that every $k$-point of $X$ is the $L$-product of some $s \in S$ with some $\iota \circ \tau$. Then $\iota$ is an open immersion.
--
--   This is the scheme-theoretic statement that a reduced closed subgroup scheme of finite index on $k$-points inside a group scheme locally of finite type over an algebraically closed field is open, the group law being encoded functorially as a relative group law on points. It is used in the construction of Néron models for $J_0(N)$ at a prime of bad reduction, where it identifies certain closed subschemes of kernels of degeneracy maps as open subschemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isOpenImmersion_of_isClosedImmersion_of_isReduced_of_finite_index.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.isOpenImmersion_of_isClosedImmersion_of_isReduced_of_finite_index
    {k : Type u} [Field k] [IsAlgClosed k] {X T : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [IsReduced X]
    (L : RelativeGroupLaw k f)
    (tT : T ⟶ Spec (CommRingCat.of k)) (ι : T ⟶ X) [IsClosedImmersion ι] (hιf : ι ≫ f = tT)
    (hmul : ∀ τ τ' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tT,
      ∃ τ'' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tT,
        L.mul (𝟙 _) ⟨τ.1 ≫ ι, by rw [Category.assoc, hιf, τ.2]⟩ ⟨τ'.1 ≫ ι, by rw [Category.assoc, hιf, τ'.2]⟩ =
          ⟨τ''.1 ≫ ι, by rw [Category.assoc, hιf, τ''.2]⟩)
    (hinv : ∀ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tT,
      ∃ τ' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tT,
        L.inv (𝟙 _) ⟨τ.1 ≫ ι, by rw [Category.assoc, hιf, τ.2]⟩ = ⟨τ'.1 ≫ ι, by rw [Category.assoc, hιf, τ'.2]⟩)
    (S : Finset (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f))
    (hidx : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, ∃ s ∈ S,
      ∃ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tT,
        x = L.mul (𝟙 _) s ⟨τ.1 ≫ ι, by rw [Category.assoc, hιf, τ.2]⟩) :
    IsOpenImmersion ι := by sorry

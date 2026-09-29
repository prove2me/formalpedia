-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation
-- name    : AlgebraicGeometry.Scheme.exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/174657d5-188f-5b03-9a9a-0ae86b49dbd9
-- title:
--   Invariant affine neighbourhood for a finite flat equivalence relation
-- statement:
--   Let $X$ and $R$ be schemes and let $s, t \colon R \to X$ be two morphisms, each assumed finite, flat and locally of finite presentation. Assume that for every scheme $T$ (in the same universe) the relation on the set of morphisms $T \to X$ defined by $x \sim y$ if and only if there exists $\varphi \colon T \to R$ with $\varphi$ followed by $s$ equal to $x$ and $\varphi$ followed by $t$ equal to $y$ is an equivalence relation, i.e. reflexive, symmetric and transitive. Let $x$ be a point of the underlying space of $X$ and let $U$ be an open subscheme (an element of `X.Opens`) which is affine, and suppose that every point $r$ of $R$ with $s(r) = x$ satisfies $t(r) \in U$; that is, the orbit $t(s^{-1}(x))$ is contained in $U$. The conclusion is that there exists an open $W$ of $X$ which is affine, contains $x$, is contained in $U$, and is invariant in the sense that the scheme-theoretic preimages $s^{-1}(W)$ and $t^{-1}(W)$ coincide as opens of $R$.
--
--   This is the local step in the construction of quotients by finite locally free equivalence relations: each point whose class lies in an affine open admits an invariant affine open neighbourhood inside that open. It is used by [`AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation`](thm.html#AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation), which glues such invariant affine opens to realise the quotient as a scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation
    {X R : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    {x : X} {U : X.Opens} (hU : IsAffineOpen U) (hx : ∀ r : R, s r = x → t r ∈ U) :
    ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ U ∧ s ⁻¹ᵁ W = t ⁻¹ᵁ W := by sorry

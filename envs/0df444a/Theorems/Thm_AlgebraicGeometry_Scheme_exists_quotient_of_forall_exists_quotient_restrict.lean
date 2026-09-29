-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict
-- name    : AlgebraicGeometry.Scheme.exists_quotient_of_forall_exists_quotient_restrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/d4ec9417-0ef3-596c-9c4c-c155e23ce884
-- title:
--   Gluing quotients along an invariant open cover
-- statement:
--   Let $X$ and $R$ be schemes and let $s, t \colon R \to X$ be two morphisms. Suppose given, for each point $x$ of $X$, an open subscheme $W x \subseteq X$ with $x \in W x$ (hypothesis `hxW`) which is invariant in the sense that the two scheme-theoretic preimages agree, $s^{-1}(W x) = t^{-1}(W x)$ (hypothesis `hinv`). Write $s \mid_{W x}$ and $t \mid_{W x}$ for the induced morphisms $s^{-1}(W x) \to W x$ and $t^{-1}(W x) \to W x$, and identify their sources by the isomorphism `R.isoOfEq (hinv x)`. Assume that for each $x$ there exist a scheme $Y$ and a morphism $p \colon W x \to Y$ such that $s \mid_{W x}$ followed by $p$ equals the transported $t \mid_{W x}$ followed by $p$, such that $p$ is finite, flat, locally of finite presentation and surjective, and such that the square formed by $s \mid_{W x}$, the transported $t \mid_{W x}$ and the two copies of $p$ is cartesian. The conclusion asserts the existence of a scheme $Y$, a morphism $p \colon X \to Y$ and a proof $w$ that $s$ followed by $p$ equals $t$ followed by $p$, such that $p$ is finite, flat, locally of finite presentation and surjective, the square with sides $s$, $t$ and two copies of $p$ is cartesian (so that $(s,t)$ identifies $R$ with $X \times_Y X$), and the cofork on $p$ determined by $w$ is a colimit, i.e. $p$ is a coequaliser of $s$ and $t$ in the category of schemes.
--
--   This is the gluing step in the construction of the quotient of a scheme by a finite locally free equivalence relation whose classes lie in affine opens (SGA 3, Exposé V, Théorème 4.1): the local quotients over an invariant open cover are patched into a global one, with no hypothesis imposed on the relation beyond the local existence of quotients, and with the coequaliser property of the local data not assumed but obtained. It is used in the proof of [`AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation`](thm.html#AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation), and its proof invokes [`AlgebraicGeometry.Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback`](thm.html#AlgebraicGeometry.Scheme.quotient_baseChange_of_finiteLocallyFree_of_isPullback), which transports such a quotient along a base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_quotient_of_forall_exists_quotient_restrict
    {X R : Scheme.{u}} (s t : R ⟶ X)
    (W : X → X.Opens) (hxW : ∀ x, x ∈ W x) (hinv : ∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x)
    (loc : ∀ x, ∃ (Y : Scheme.{u}) (p : (W x).toScheme ⟶ Y),
      (s ∣_ W x) ≫ p = ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) ≫ p ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (s ∣_ W x) ((R.isoOfEq (hinv x)).hom ≫ (t ∣_ W x)) p p) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by sorry

-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_exists_forall_isAffineOpen_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent
-- name    : AlgebraicGeometry.Smooth.exists_forall_isAffineOpen_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/1ab0c70a-f7ba-59cc-8fa1-c53e657a76b4
-- title:
--   Local smooth lifting along a nilpotent surjection
-- statement:
--   Let $p : S \to S_0$ be a surjective homomorphism of commutative rings (in a fixed universe) every element of whose kernel is nilpotent, let $X_0$ be a scheme, and let $f_0 : X_0 \to \operatorname{Spec} S_0$ be a smooth morphism (in Mathlib's sense of the `Smooth` morphism property), and let $x$ be a point of $X_0$. Then there exists an open subset $U$ of $X_0$ containing $x$ such that $U$ is an affine open, and such that for every open subset $V \subseteq U$ of $X_0$ which is an affine open there exist a scheme $Y$, a morphism $q : Y \to \operatorname{Spec} S$ and a morphism $g : V \to Y$ from the open subscheme $V$, with $Y$ affine, $q$ smooth, and the square with sides $g$, the composite of the inclusion $V \hookrightarrow X_0$ followed by $f_0$, $q$ and $\operatorname{Spec}(p)$ a pullback square (`IsPullback g (V.ι ≫ f₀) q (Spec.map (CommRingCat.ofHom p))`). Thus $Y$ is an affine smooth lift of $V$ over $S$ and $g$ identifies $V$ with $Y \times_{\operatorname{Spec} S} \operatorname{Spec} S_0$. Note that the affine open neighbourhood $U$ is chosen uniformly: the lifting property is asserted for all affine opens contained in it.
--
--   This is the local existence statement in the deformation theory of smooth morphisms: a smooth scheme over $S_0$ lifts smoothly over $S$ locally on the source, along a surjection with nilpotent kernel. It feeds the construction of a cover of $X_0$ by affine opens each of which admits such a smooth lift, in [`AlgebraicGeometry.Smooth.exists_orderedAffineCover_forall_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent`](thm.html#AlgebraicGeometry.Smooth.exists_orderedAffineCover_forall_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_exists_forall_isAffineOpen_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Smooth.exists_forall_isAffineOpen_exists_smooth_isPullback_of_surjective_of_forall_isNilpotent
    {S S₀ : Type u} [CommRing S] [CommRing S₀] (p : S →+* S₀) (hp : Function.Surjective p)
    (hnil : ∀ x ∈ RingHom.ker p, IsNilpotent x)
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of S₀)) [Smooth f₀] (x : X₀) :
    ∃ U : X₀.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∀ V : X₀.Opens, IsAffineOpen V → V ≤ U →
        ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of S)) (g : (V : Scheme.{u}) ⟶ Y),
          IsAffine Y ∧ Smooth q ∧ IsPullback g (V.ι ≫ f₀) q (Spec.map (CommRingCat.ofHom p)) := by sorry

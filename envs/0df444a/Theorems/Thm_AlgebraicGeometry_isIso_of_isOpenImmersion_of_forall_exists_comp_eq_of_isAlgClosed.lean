-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_of_isOpenImmersion_of_forall_exists_comp_eq_of_isAlgClosed
-- name    : AlgebraicGeometry.isIso_of_isOpenImmersion_of_forall_exists_comp_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/036bc5bd-af3f-5a79-9fd2-34c118598cd3
-- title:
--   Open immersion surjective on Ω-points is an isomorphism
-- statement:
--   Let $K$ and $\Omega$ be fields in a fixed universe, with $\Omega$ a $K$-algebra which is algebraically closed. Let $X$ and $Y$ be schemes, let $gY : Y \to \operatorname{Spec} K$ be a morphism which is locally of finite type (Mathlib's `LocallyOfFiniteType` class on $gY$), and let $i : X \to Y$ be an open immersion. Assume that every $\Omega$-valued point of $Y$ defined over $K$ lifts through $i$: for every morphism $y : \operatorname{Spec}\Omega \to Y$ such that $y \circ gY$ (in Lean's diagrammatic order, $y \gg gY$) equals the structure morphism $\operatorname{Spec}$ of the algebra map $K \to \Omega$, there exists $x : \operatorname{Spec}\Omega \to X$ with $x \gg i = y$. The conclusion is that $i$ is an isomorphism of schemes, i.e. `IsIso i`. Note that $X$ is not assumed to be of finite type or even non-empty separately; these follow from the open immersion together with the lifting hypothesis.
--
--   This is the standard criterion that an open subscheme of a $K$-scheme locally of finite type which captures all $\Omega$-valued points, for $\Omega$ an algebraically closed extension of $K$, is the whole scheme. In this development it is used to identify open subschemes of coarse moduli spaces of quaternionic Shimura curves with the whole space, in the Čerednik–Drinfeld part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_of_isOpenImmersion_of_forall_exists_comp_eq_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isOpenImmersion_of_forall_exists_comp_eq_of_isAlgClosed
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType gY]
    (i : X ⟶ Y) [IsOpenImmersion i]
    (hsurj : ∀ y : Spec (CommRingCat.of Ω) ⟶ Y, y ≫ gY = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) →
      ∃ x : Spec (CommRingCat.of Ω) ⟶ X, x ≫ i = y) :
    IsIso i := by sorry

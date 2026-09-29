-- Prove2me | Theorems.Thm_AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_surjective_of_locallyOfFiniteType
-- name    : AlgebraicGeometry.FormallyUnramified.eq_of_comp_eq_of_surjective_of_locallyOfFiniteType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/f769661d-0f15-5d38-ba58-8c26407fe1d0
-- title:
--   Unramified morphisms: uniqueness of maps after surjective base change
-- statement:
--   Let $X$, $Y$, $T$, $T_0$ be schemes (in a fixed universe) and let $f : X \to Y$ be a morphism which is formally unramified and locally of finite type, the two conditions being imposed as typeclass hypotheses `FormallyUnramified f` and `LocallyOfFiniteType f`. Let $j : T_0 \to T$ be a morphism which is surjective, in the sense of Mathlib's `Surjective` class for scheme morphisms (the underlying continuous map is surjective). Let $u, u' : T \to X$ be two morphisms such that $u$ followed by $f$ equals $u'$ followed by $f$, and such that $j$ followed by $u$ equals $j$ followed by $u'$. The conclusion is that $u = u'$ as morphisms of schemes. Thus two $T$-points of $X$ lying over the same $T$-point of $Y$ which agree after pullback along an arbitrary surjection $T_0 \to T$ coincide; no flatness, finiteness or nilpotence hypothesis on $j$ is required, only surjectivity on underlying topological spaces.
--
--   This is the uniqueness half of the classical statement that an unramified morphism admits at most one lift across a thickening (EGA IV, 17.1; Stacks 02GE), in the strong form where the thickening is replaced by an arbitrary surjection of underlying spaces. It is used in the construction of fake elliptic curves in the Čerednik–Drinfel'd part of the development, to show that maps out of a base defined by a nilpotent ideal are determined by their reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_surjective_of_locallyOfFiniteType.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.FormallyUnramified.eq_of_comp_eq_of_surjective_of_locallyOfFiniteType
    {X Y T T₀ : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (j : T₀ ⟶ T) [Surjective j] (u u' : T ⟶ X) (hf : u ≫ f = u' ≫ f) (hj : j ≫ u = j ≫ u') :
    u = u' := by sorry

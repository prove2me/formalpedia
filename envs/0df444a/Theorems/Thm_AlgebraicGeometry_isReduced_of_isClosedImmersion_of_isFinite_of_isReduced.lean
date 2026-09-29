-- Prove2me | Theorems.Thm_AlgebraicGeometry_isReduced_of_isClosedImmersion_of_isFinite_of_isReduced
-- name    : AlgebraicGeometry.isReduced_of_isClosedImmersion_of_isFinite_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/13c2ff9f-6a12-57a4-a65a-ccf6137838c2
-- title:
--   Closed subschemes of finite reduced k-schemes are reduced
-- statement:
--   Let $k$ be a field and let $X$, $Z$ be schemes whose underlying type lives in the same universe as $k$. Suppose given a morphism $f : X \to \operatorname{Spec} k$ (with $k$ regarded as an object of `CommRingCat`) which is finite, i.e. satisfies Mathlib's `IsFinite` predicate for morphisms of schemes, and suppose that $X$ is reduced in the sense of `IsReduced`, namely that $X$ is nonempty and the ring of sections over each open subset has no nonzero nilpotents. Suppose further given a morphism $i : Z \to X$ which is a closed immersion in the sense of `IsClosedImmersion`. The conclusion is that $Z$ is then reduced, again in the sense of the scheme-theoretic predicate `IsReduced`.
--
--   This is the standard fact that a closed subscheme of a reduced scheme finite over a field is reduced, the point being that the global sections of such an $X$ form a reduced Artinian ring, hence a finite product of fields, all of whose quotients are reduced. It serves as a basic tool for handling closed subschemes (kernels, intersections) of finite reduced group schemes over a field, and is used in the construction of transverse level lifts for fake elliptic curves in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isReduced_of_isClosedImmersion_of_isFinite_of_isReduced.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isReduced_of_isClosedImmersion_of_isFinite_of_isReduced
    {k : Type u} [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f] [IsReduced X]
    (i : Z ⟶ X) [IsClosedImmersion i] : IsReduced Z := by sorry

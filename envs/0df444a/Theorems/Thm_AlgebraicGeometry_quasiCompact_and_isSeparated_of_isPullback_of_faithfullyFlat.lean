-- Prove2me | Theorems.Thm_AlgebraicGeometry_quasiCompact_and_isSeparated_of_isPullback_of_faithfullyFlat
-- name    : AlgebraicGeometry.quasiCompact_and_isSeparated_of_isPullback_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/4f91d7be-1acc-56b5-bc92-03d05adaceec
-- title:
--   Descent of quasi-compactness and separatedness along faithfully flat base change
-- statement:
--   Let $S$ and $S'$ be commutative rings in a fixed universe, with $S'$ an $S$-algebra which is faithfully flat as an $S$-module. Let $X$ and $X'$ be schemes, and let $f : X \to \operatorname{Spec} S$, $f' : X' \to \operatorname{Spec} S'$ and $c : X' \to X$ be morphisms of schemes such that the square formed by $c$, $f'$, $f$ and the morphism $\operatorname{Spec} S' \to \operatorname{Spec} S$ induced by the structure map $S \to S'$ is cartesian, i.e. $c$ followed by $f$ equals $f'$ followed by $\operatorname{Spec}$ of $S \to S'$, and this square exhibits $X'$ as the fibre product $X \times_{\operatorname{Spec} S} \operatorname{Spec} S'$. Assume $f'$ is quasi-compact and separated, separatedness being in Mathlib's sense that the diagonal $X' \to X' \times_{\operatorname{Spec} S'} X'$ is a closed immersion. The conclusion is that $f$ is quasi-compact and separated in the same senses.
--
--   This is the descent of quasi-compactness and of separatedness of a morphism along a faithfully flat base change, here in the special case of a base change of affine bases $\operatorname{Spec} S' \to \operatorname{Spec} S$. It is used in the construction of the closed immersion given by sections over a faithfully flat base change, and in the construction of quotients of schemes by a finite Galois group action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_quasiCompact_and_isSeparated_of_isPullback_of_faithfullyFlat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.quasiCompact_and_isSeparated_of_isPullback_of_faithfullyFlat
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    [QuasiCompact f'] [IsSeparated f'] :
    QuasiCompact f ∧ IsSeparated f := by sorry

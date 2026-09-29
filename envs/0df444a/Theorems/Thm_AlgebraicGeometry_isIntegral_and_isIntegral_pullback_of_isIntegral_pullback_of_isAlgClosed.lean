-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIntegral_and_isIntegral_pullback_of_isIntegral_pullback_of_isAlgClosed
-- name    : AlgebraicGeometry.isIntegral_and_isIntegral_pullback_of_isIntegral_pullback_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/922688f1-16f7-59f3-9226-00c28efb4c5c
-- title:
--   Integrality of one algebraically closed base change suffices
-- statement:
--   Let $K$ be a field, let $X$ be a scheme (in the bottom universe) and let $\pi_X : X \to \operatorname{Spec} K$ be a morphism that is locally of finite type. Let $L$ be an algebraically closed field equipped with a $K$-algebra structure, and form the fibre product of $\pi_X$ with the morphism $\operatorname{Spec} L \to \operatorname{Spec} K$ induced by the structure map $K \to L$, i.e. the categorical pullback $X_L$ in the category of schemes. The hypothesis is that this pullback is an integral scheme (irreducible and reduced, in Mathlib's sense of `IsIntegral`). The conclusion is the conjunction of two assertions: first, $X$ itself is integral; second, for every algebraically closed field $k$ equipped with a $K$-algebra structure, the pullback of $\pi_X$ along $\operatorname{Spec} k \to \operatorname{Spec} K$ is integral. Thus integrality of a single algebraically closed base change propagates both downwards to $X$ and across to all algebraically closed base changes; no hypothesis is placed on the characteristic of $K$, and the algebraic closedness of $L$ is essential.
--
--   This is the standard statement that, for a scheme locally of finite type over a field, geometric integrality can be tested on one algebraically closed base change (EGA IV 4.5.9, 4.6.1), together with the descent of integrality to the base. It is used in the corresponding statement for smooth proper morphisms, [`AlgebraicGeometry.isIntegral_and_isIntegral_pullback_of_smooth_isProper_of_isIntegral_pullback`](thm.html#AlgebraicGeometry.isIntegral_and_isIntegral_pullback_of_smooth_isProper_of_isIntegral_pullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIntegral_and_isIntegral_pullback_of_isIntegral_pullback_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIntegral_and_isIntegral_pullback_of_isIntegral_pullback_of_isAlgClosed
    (K : Type) [Field K] (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType πX]
    (L : Type) [Field L] [IsAlgClosed L] [Algebra K L]
    (hL : IsIntegral (CategoryTheory.Limits.pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K L))))) :
    IsIntegral X ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra K k],
        IsIntegral (CategoryTheory.Limits.pullback πX (Spec.map (CommRingCat.ofHom (algebraMap K k)))) := by sorry

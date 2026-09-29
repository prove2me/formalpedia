-- Prove2me | Theorems.Thm_Algebra_norm_one_add_eps_tmul
-- name    : Algebra.norm_one_add_eps_tmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/50841da1-4cdd-5363-9673-f8bbb992902e
-- title:
--   Norm of 1+ε⊗ f equals 1+ε Tr(f)
-- statement:
--   Let $A'$ and $B$ be commutative rings in a fixed universe, with $B$ an $A'$-algebra that is free and finite as an $A'$-module, and let $f \in B$. Write $A'[\varepsilon] =$ `DualNumber A'`, the trivial square-zero extension of $A'$ by $A'$, with $\varepsilon =$ `DualNumber.eps` satisfying $\varepsilon^2 = 0$, and consider the $A'[\varepsilon]$-algebra $A'[\varepsilon] \otimes_{A'} B$ obtained by base change (Mathlib's tensor-product algebra structure, with $A'[\varepsilon]$ acting on the left factor). The assertion is an identity in $A'[\varepsilon]$: the algebra norm over $A'[\varepsilon]$ of the element $1 + \varepsilon \otimes_{A'} f$ of $A'[\varepsilon] \otimes_{A'} B$, that is, the determinant of left multiplication by that element on $A'[\varepsilon] \otimes_{A'} B$ viewed as an $A'[\varepsilon]$-module, equals $1 + \mathrm{inr}(\mathrm{Tr}_{B/A'}(f))$, where $\mathrm{Tr}_{B/A'}$ is the algebra trace of $B$ over $A'$ and $\mathrm{inr}$ is the inclusion of $A'$ into the square-zero part of $A'[\varepsilon]$, so that the right-hand side is $1 + \varepsilon\,\mathrm{Tr}_{B/A'}(f)$.
--
--   This is the first-order expansion of the algebra norm: the tangent map of the norm of a finite free algebra is the trace. It is used in the relative Picard/deformation computations, where it is cited by [`AlgebraicGeometry.RelPicard.exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul`](thm.html#AlgebraicGeometry.RelPicard.exists_isFrameOn_normModule_and_map_eq_oneAddEpsMul_trace_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_norm_one_add_eps_tmul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open scoped TensorProduct

theorem Algebra.norm_one_add_eps_tmul
    (A' B : Type u) [CommRing A'] [CommRing B] [Algebra A' B] [Module.Free A' B] [Module.Finite A' B] (f : B) :
    Algebra.norm (DualNumber A') ((1 : DualNumber A' ⊗[A'] B) + (DualNumber.eps : DualNumber A') ⊗ₜ[A'] f) =
      1 + TrivSqZeroExt.inr (Algebra.trace A' B f) := by sorry

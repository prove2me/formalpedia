-- Prove2me | Theorems.Thm_Algebra_IsSmoothAt_flat_localization_atPrime
-- name    : Algebra.IsSmoothAt.flat_localization_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/6fcccfb9-7c3a-5e51-9d4d-337c1f99927a
-- title:
--   Smoothness at a prime implies flatness of the local ring
-- statement:
--   Let $R$ and $A$ be commutative rings with $A$ an $R$-algebra that is of finite presentation over $R$, and let $\mathfrak p \subseteq A$ be a prime ideal at which the $R$-algebra $A$ is smooth, in the sense of Mathlib's `Algebra.IsSmoothAt R p`. The conclusion is that the localisation $A_{\mathfrak p} =$ `Localization.AtPrime p` is flat as an $R$-module.
--
--   This is the standard fact that a finitely presented algebra which is smooth at a prime is flat over the base there, the local form of "smooth implies flat" (EGA IV 17.5.1). It is used on the way to producing sections with prescribed behaviour at a smooth point of a curve, via [`AlgebraicCurve.exists_section_localRing_apply_eq_of_ord_eq_one_of_mem_smoothLocus`](thm.html#AlgebraicCurve.exists_section_localRing_apply_eq_of_ord_eq_one_of_mem_smoothLocus).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsSmoothAt_flat_localization_atPrime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Algebra

theorem Algebra.IsSmoothAt.flat_localization_atPrime (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (p : Ideal A) [p.IsPrime] [Algebra.IsSmoothAt R p] :
    Module.Flat R (Localization.AtPrime p) := by sorry

-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsFinite_of_isProper_of_finite_preimage_closedPoint
-- name    : AlgebraicGeometry.IsFinite.of_isProper_of_finite_preimage_closedPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/9d671638-2fab-58bd-83c6-4203954bc4e6
-- title:
--   Proper over a local ring with finite closed fibre is finite
-- statement:
--   Let $R$ be a commutative ring (in universe $u$) equipped with the hypothesis that it is a local ring, and let $X$ be a scheme in universe $u$. Let $f \colon X \to \operatorname{Spec} R$ be a morphism of schemes, where $\operatorname{Spec} R$ is the spectrum of $R$ viewed as a commutative ring object, and assume that $f$ is proper in the sense of Mathlib's `IsProper` class. Assume further that the preimage, under the continuous map of underlying topological spaces attached to $f$, of the singleton consisting of the closed point of $\operatorname{Spec} R$ (the point given by the maximal ideal of $R$) is a finite subset of $X$; that is, the fibre of $f$ over the closed point has finitely many points as a set. The conclusion is that $f$ is a finite morphism, `IsFinite f`. No flatness, no Noetherian hypothesis and no finiteness assumption on the other fibres are imposed: finiteness of the single closed fibre as a set, together with properness, suffices.
--
--   This is the standard rigidity-type criterion (EGA IV₃ 13.1.4–13.1.5): over a local base, a proper morphism whose closed fibre is a finite set is quasi-finite, hence finite. It is used in the project to establish a factorisation criterion for morphisms into a proper $\operatorname{Spec} R$-scheme through the quotients of $R$ by the powers of its maximal ideal, in [`AlgebraicGeometry.exists_comp_eq_iff_of_forall_quotient_maximalIdeal_pow_of_isProper`](thm.html#AlgebraicGeometry.exists_comp_eq_iff_of_forall_quotient_maximalIdeal_pow_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsFinite_of_isProper_of_finite_preimage_closedPoint.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicGeometry.IsFinite.of_isProper_of_finite_preimage_closedPoint
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hfin : (f.base ⁻¹' {(IsLocalRing.closedPoint R : PrimeSpectrum R)}).Finite) :
    IsFinite f := by sorry

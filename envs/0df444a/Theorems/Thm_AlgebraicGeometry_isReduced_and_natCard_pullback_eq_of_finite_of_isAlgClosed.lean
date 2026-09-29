-- Prove2me | Theorems.Thm_AlgebraicGeometry_isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed
-- name    : AlgebraicGeometry.isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/27007d3b-4e1d-5707-a64e-271d1ef44be6
-- title:
--   Points and reducedness under algebraically closed base change
-- statement:
--   Let $k_0$ be an algebraically closed field (in a fixed universe), let $Z$ be a scheme and let $z \colon Z \to \operatorname{Spec} k_0$ be a morphism that is locally of finite type; assume $Z$ is reduced and that the underlying topological space of $Z$ is finite. Let $k$ be a further algebraically closed field in the same universe and let $\iota \colon k_0 \to k$ be a ring homomorphism, giving the morphism $\operatorname{Spec} k \to \operatorname{Spec} k_0$ induced by $\iota$. The assertion is the conjunction of two statements about the fibre product $Z \times_{\operatorname{Spec} k_0} \operatorname{Spec} k$, formed as the categorical pullback of $z$ along that morphism: first, this pullback scheme is reduced; second, the number of points of its underlying topological space equals the number of points of the underlying space of $Z$, the equality being one of natural-number cardinalities (`Nat.card` of the two point sets, which the hypotheses force to be finite and nonzero-free in the usual sense).
--
--   This is the statement that a finite reduced scheme locally of finite type over an algebraically closed field stays reduced and keeps its number of points under base change to a larger algebraically closed field; classically it follows from $Z$ being the spectrum of $k_0^{\#|Z|}$. It supplies the counting and reducedness input for the transport of two-component degenerate fibres, being cited by [`AlgebraicGeometry.exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed`](thm.html#AlgebraicGeometry.exists_twoGluedSmoothCurveDegeneration_of_factor_of_isAlgClosed) and by [`ModularCurve.XHDRModelAtP.exists_twoGluedSmoothCurves_isReduced_pullback_of_ker_ne_bot`](thm.html#ModularCurve.XHDRModelAtP.exists_twoGluedSmoothCurves_isReduced_pullback_of_ker_ne_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed
    {k₀ : Type u} [Field k₀] [IsAlgClosed k₀] {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of k₀))
    [LocallyOfFiniteType z] [IsReduced Z] [Finite ↥Z]
    {k : Type u} [Field k] [IsAlgClosed k] (ι : k₀ →+* k) :
    IsReduced (pullback z (Spec.map (CommRingCat.ofHom ι))) ∧
      Nat.card ↥(pullback z (Spec.map (CommRingCat.ofHom ι))) = Nat.card ↥Z := by sorry

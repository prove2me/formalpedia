-- Prove2me | Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing
-- name    : AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/7ee49faf-06f3-57ba-a783-eaaff24c575c
-- title:
--   Degree zero base change over an arbitrary local base
-- statement:
--   Let $X$ be a scheme and let $A$ be a commutative ring which is local, with maximal ideal $\mathfrak{m} =$ `IsLocalRing.maximalIdeal A`. Let $p : X \to \operatorname{Spec} A$ be a morphism of schemes which is proper, flat and locally of finite presentation. Form the base change of $p$ along $\operatorname{Spec}$ of the quotient map $A \to A/\mathfrak{m}$, and let $\operatorname{pullback.snd}$ denote the resulting projection $X \times_{\operatorname{Spec} A} \operatorname{Spec}(A/\mathfrak{m}) \to \operatorname{Spec}(A/\mathfrak{m})$ from the closed fibre. The hypothesis is that the induced map on global sections of this projection, i.e. the ring map $A/\mathfrak{m} \to \Gamma\bigl(X \times_{\operatorname{Spec} A} \operatorname{Spec}(A/\mathfrak{m}), \mathcal{O}\bigr)$, is bijective. The conclusion is that the map on global sections induced by $p$ itself, the ring map $A \to \Gamma(X, \mathcal{O}_X)$, is bijective. No Noetherian hypothesis is imposed on $A$; finite presentation of $p$ replaces it.
--
--   This is the degree-zero case of cohomology and base change over a local base: a proper flat morphism of finite presentation whose closed fibre has only constant global functions has only constant global functions. It extends the Noetherian local statement [`AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing`](thm.html#AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing) to arbitrary local rings, and is used to identify the ring of global sections of fake elliptic curves and of Jacobians with good reduction, and in the globalised form [`AlgebraicGeometry.bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField`](thm.html#AlgebraicGeometry.bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_locallyOfFinitePresentation_of_isLocalRing
    {X : Scheme.{u}} {A : CommRingCat.{u}} [IsLocalRing A]
    (p : X ⟶ Spec A) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    (h : Function.Bijective (pullback.snd p (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))).appTop) :
    Function.Bijective p.appTop := by sorry

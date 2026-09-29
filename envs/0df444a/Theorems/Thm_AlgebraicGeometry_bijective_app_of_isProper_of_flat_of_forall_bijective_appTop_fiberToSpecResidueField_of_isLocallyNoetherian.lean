-- Prove2me | Theorems.Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField_of_isLocallyNoetherian
-- name    : AlgebraicGeometry.bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField_of_isLocallyNoetherian
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/edf6340c-0849-5dc5-9ecc-49025429a5d6
-- title:
--   mathcal O_B → p_*mathcal O_X bijective over a locally Noetherian base
-- statement:
--   Let $X$ and $B$ be schemes (in a fixed universe) with $B$ locally Noetherian, and let $p \colon X \to B$ be a morphism that is proper, flat and locally of finite presentation. Assume that for every point $b$ of $B$ the morphism `p.fiberToSpecResidueField b`, namely the structure morphism of the fibre $X_b = X \times_B \operatorname{Spec}\kappa(b)$ over $\operatorname{Spec}$ of the residue field $\kappa(b)$ at $b$, induces a bijection on global sections, i.e. the canonical ring map $\kappa(b) \to \Gamma(X_b, \mathcal O_{X_b})$ is bijective. Then for every open subscheme $U$ of $B$ the ring homomorphism `p.app U`, that is the component at $U$ of $\mathcal O_B \to p_*\mathcal O_X$, $\Gamma(U, \mathcal O_B) \to \Gamma(p^{-1}(U), \mathcal O_X)$, is bijective. Since this holds for all opens $U$, the statement says exactly that the unit $\mathcal O_B \to p_*\mathcal O_X$ is an isomorphism of sheaves of rings on $B$.
--
--   This is the degree-zero case of cohomology and base change: a proper flat morphism of finite presentation over a locally Noetherian base whose fibres have trivial $H^0$ satisfies $\mathcal O_B \xrightarrow{\sim} p_*\mathcal O_X$. It is the form of the result used to derive the same conclusion from geometric reducedness and geometric connectedness of the fibres, for instance when identifying structure sheaves of pushforwards along proper flat families of curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField_of_isLocallyNoetherian.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField_of_isLocallyNoetherian
    {X B : Scheme.{u}} [IsLocallyNoetherian B] (p : X ⟶ B) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    (h : ∀ b : B, Function.Bijective (p.fiberToSpecResidueField b).appTop) (U : B.Opens) :
    Function.Bijective (p.app U) := by sorry

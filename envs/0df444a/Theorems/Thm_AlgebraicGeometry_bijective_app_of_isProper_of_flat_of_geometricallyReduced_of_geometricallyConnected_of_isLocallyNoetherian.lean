-- Prove2me | Theorems.Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_of_isLocallyNoetherian
-- name    : AlgebraicGeometry.bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_of_isLocallyNoetherian
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/3904db0d-e445-5baf-8782-30522ad137a6
-- title:
--   Proper flat morphisms with geometrically reduced connected fibres: mathcal O_B ≅ p_*mathcal O_X
-- statement:
--   Let $X$ and $B$ be schemes (in a fixed universe) with $B$ locally Noetherian, and let $p \colon X \to B$ be a morphism which is proper, flat and locally of finite presentation, and which satisfies the morphism properties `GeometricallyReduced` and `GeometricallyConnected`, i.e. whose fibres are geometrically reduced and geometrically connected. Then for every open subset $U$ of $B$ the ring homomorphism $p^\sharp_U \colon \Gamma(U, \mathcal O_B) \to \Gamma(p^{-1}(U), \mathcal O_X)$ induced by $p$ on sections over $U$, written `p.app U`, is bijective. Equivalently, the canonical map $\mathcal O_B \to p_*\mathcal O_X$ is an isomorphism of sheaves of rings on $B$; the assertion is made for every single open $U$ of $B$, not merely for $U = B$ or on a basis of opens.
--
--   This is the classical statement that a proper flat morphism of finite presentation with geometrically reduced and geometrically connected (for instance geometrically integral) fibres over a locally Noetherian base satisfies $\mathcal O_B \xrightarrow{\ \sim\ } p_*\mathcal O_X$, the form in which Stein-type rigidity arguments are usually applied. Within the project it is used by [`GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_comp_eq_of_isNilpotent_ker_of_isNoetherianRing`](thm.html#GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_comp_eq_of_isNilpotent_ker_of_isNoetherianRing), in the construction of the group law on the relative Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_of_isLocallyNoetherian.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_of_isLocallyNoetherian
    {X B : Scheme.{u}} [IsLocallyNoetherian B] (p : X ⟶ B) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [GeometricallyReduced p] [GeometricallyConnected p] (U : B.Opens) :
    Function.Bijective (p.app U) := by sorry

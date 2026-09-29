-- Prove2me | Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_smooth_of_geometricallyConnected
-- name    : AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyConnected
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/c19d5c6b-241c-5e2d-883f-dd3ea0bbab2d
-- title:
--   Smooth with geometrically connected fibres implies geometrically integral
-- statement:
--   Let $X$ and $S$ be schemes in a fixed universe and let $f\colon X \to S$ be a morphism which is smooth and geometrically connected, so that every base change of $f$ along a morphism from the spectrum of a field is a connected scheme. The conclusion is that $f$ is geometrically integral in Mathlib's sense: for every field $K$, every morphism $y\colon \operatorname{Spec} K \to S$, and every scheme $Z$ equipped with morphisms $Z \to X$ and $Z \to \operatorname{Spec} K$ making the resulting square a pullback square over $f$ and $y$ — that is, for every realisation of the fibre product $X \times_S \operatorname{Spec} K$, not merely for the canonical one — the scheme $Z$ is integral, i.e. irreducible and reduced. No Noetherian, finite-type or separatedness assumption is imposed on $f$ or on $S$ beyond smoothness, which is taken in the sense of Mathlib's morphism property `Smooth`.
--
--   This is the standard criterion that a smooth morphism with geometrically connected fibres has geometrically integral fibres (EGA IV 4.5.13, 17.5.7). It is used downstream to obtain integrality of base changes and of pullbacks of smooth $S$-schemes, for instance in the arguments about Stein-type factorisations and abelian schemes over a discrete valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_geometricallyIntegral_of_smooth_of_geometricallyConnected.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyConnected
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] :
    GeometricallyIntegral f := by sorry

-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
-- name    : AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/28db19f0-708d-5042-8433-8acf40b128de
-- title:
--   Stalks of a smooth scheme over a DVR are integrally closed domains
-- statement:
--   Let $R$ be a commutative ring which is an integral domain and a discrete valuation ring, let $T$ be a scheme (in the same universe), and let $t \colon T \to \operatorname{Spec} R$ be a morphism of schemes which is smooth, in the sense of Mathlib's `Smooth` class for morphisms of schemes. Then for every point $x$ of $T$ the stalk $\mathcal{O}_{T,x} =$ `T.presheaf.stalk x` of the structure sheaf at $x$ is an integral domain and is integrally closed in its field of fractions. Both assertions are delivered together as a conjunction; no Noetherian or finite-type hypothesis beyond smoothness of $t$ is imposed, and nothing is asserted about regularity of the stalk.
--
--   This is the statement that a scheme smooth over a discrete valuation ring is normal (EGA IV 6.5.4), specialised to stalks and in the form 'domain and integrally closed'. It is the normality input used elsewhere in the development, for instance in the study of invertible modules on schemes over a discrete valuation ring and in the recognition of stalks as discrete valuation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] (x : T) :
    IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x) := by sorry

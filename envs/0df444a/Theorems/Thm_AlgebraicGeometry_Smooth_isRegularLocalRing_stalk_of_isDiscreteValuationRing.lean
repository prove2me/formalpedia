-- Prove2me | Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing
-- name    : AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/e305a401-45d5-5413-9f6a-ccb10bf897cb
-- title:
--   Stalks of a scheme smooth over a DVR are regular
-- statement:
--   Let $R$ be a commutative ring which is a domain and a discrete valuation ring, let $T$ be a scheme (in the fixed universe $u$), let $t \colon T \to \operatorname{Spec} R$ be a morphism of schemes, where $\operatorname{Spec} R$ is the spectrum of $R$ viewed as an object of `CommRingCat`, and assume that $t$ is smooth in the sense of Mathlib's `Smooth` class for morphisms of schemes. Let $x$ be a point of $T$. The conclusion is that the stalk $\mathcal{O}_{T,x}$ of the structure sheaf of $T$ at $x$, formed as `T.presheaf.stalk x`, is a regular local ring, i.e. satisfies `IsRegularLocalRing`. No Noetherian, finite-type or separatedness hypothesis on $T$ beyond what smoothness of $t$ supplies is imposed, and no condition on the residue characteristic or on the image of $x$ in $\operatorname{Spec} R$ is imposed.
--
--   This is the case of a discrete valuation ring base of the statement that a scheme smooth over a regular base is regular (EGA IV, 17.5.8). It supplies regularity of local rings on smooth models over $\mathbb{Z}_p$-like bases and is invoked throughout the treatment of good reduction of Jacobians, relative group laws and integral models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] (x : T) :
    IsRegularLocalRing (T.presheaf.stalk x) := by sorry

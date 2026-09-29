-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_snd_apply_eq_and_notMem_support
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/de77d543-9b51-55dc-8886-8a14ce836e6d
-- title:
--   A relative effective divisor misses a point in each fibre
-- statement:
--   Let $R$ be a commutative ring, let $C$ be a scheme and let $c : C \to \operatorname{Spec} R$ be proper, smooth of relative dimension $1$ and geometrically irreducible; let $T$ be a scheme with a morphism $t : T \to \operatorname{Spec} R$, let $d$ be a natural number, and let $D$ be a relative effective Cartier divisor of degree $d$ for $c$ over $t$, that is: an ideal sheaf datum $D.I$ on the fibre product $C \times_{\operatorname{Spec} R} T$ such that the composite of the closed immersion `D.I.subschemeι` of the associated closed subscheme with the second projection `pullback.snd c t` is finite, flat and locally of finite presentation, and has rank $d$ at every point of $T$. Then for every point $x$ of $T$ there exists a point $y$ of the underlying space of $C \times_{\operatorname{Spec} R} T$ whose image under the map of topological spaces underlying `pullback.snd c t` is $x$ and which does not lie in the support of $D.I$.
--
--   This is the elementary statement that a degree-$d$ relative effective divisor on a smooth proper relative curve, having finite fibres over the base, cannot exhaust the fibre of the curve over any point. It is used in the comparison of relative effective divisors with line bundles on the relative Picard functor, where a point of the fibre away from the divisor's support serves as a base point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelEffCartierDiv.exists_snd_apply_eq_and_notMem_support
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {d : ℕ} (D : RelEffCartierDiv c d t) (x : T) :
    ∃ y : ↥(pullback c t), (pullback.snd c t).base y = x ∧ y ∉ D.I.support := by sorry

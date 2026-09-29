-- Prove2me | Theorems.Thm_AlgebraicCurve_traceDiff_apply
-- name    : AlgebraicCurve.traceDiff_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/273b6e13-d843-5388-b552-189ee68baf58
-- title:
--   Defining property of the trace map on differentials
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ algebras over $K$ and $F'$ an algebra over $F$, the two $K$-algebra structures on $F'$ being compatible (a scalar tower $K \to F \to F'$), and assume $F'$ is separable over $F$. Let $y \in F'$ and let $\omega \in \Omega_{F/K}$ be a Kähler differential of $F$ over $K$. The map `traceDiff K F F'` is, by definition, an $F$-linear map $\Omega_{F'/K} \to \Omega_{F/K}$ chosen to satisfy the predicate `IsTraceDiff`, namely $t(y \cdot \mathrm{d}\text{-pullback}(\omega)) = \mathrm{Tr}_{F'/F}(y) \cdot \omega$ for all $y$ and $\omega$, if such a map exists, and is the zero map otherwise. The assertion is that this chosen map does satisfy that identity for the given data: the image under `traceDiff K F F'` of $y \cdot \mathrm{KaehlerDifferential.map}\,K\,K\,F\,F'(\omega)$, the pull-back of $\omega$ to $\Omega_{F'/K}$ scaled by $y$, equals $\mathrm{Tr}_{F'/F}(y) \cdot \omega$, where the trace is Mathlib's `Algebra.trace F F'`. No finiteness of $F'$ over $F$ is assumed; for extensions that are not finite the trace form is zero and the identity is read with both sides vanishing.
--
--   This is the characteristic property of the trace (cotrace) map on differentials of a separable extension, in the function-field formulation of curves, and it is the only way the choice-totalised map `traceDiff` is evaluated. It is used downstream to identify `traceDiff` with the trace along a morphism and in the $q$-expansion computations for differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_traceDiff_apply.lean

import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.traceDiff_apply (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] (y : F') (ω : Ω[F⁄K]) : traceDiff K F F' (y • KaehlerDifferential.map K K F F' ω) = Algebra.trace F F' y • ω := by sorry

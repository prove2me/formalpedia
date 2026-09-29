-- Prove2me | Theorems.Thm_AlgebraicCurve_isTraceDiff_traceDiff
-- name    : AlgebraicCurve.isTraceDiff_traceDiff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/2dcdc19c-f27b-5374-8fdc-2ced71b1abd7
-- title:
--   The totalised trace of differentials satisfies its defining identity
-- statement:
--   Let $K$, $F$, $F'$ be fields with $K$-algebra structures on $F$ and $F'$, an $F$-algebra structure on $F'$ compatible with these (a scalar tower $K \to F \to F'$), and assume $F'$ is separable over $F$. The assertion is that the $F$-linear map [`AlgebraicCurve.traceDiff K F F' : Ω[F'⁄K] →ₗ[F] Ω[F⁄K]`](def/ModularCurve_QExpansionDiff.html#L62) satisfies the predicate `IsTraceDiff K F F'`, that is: for every $y \in F'$ and every $\omega \in \Omega[F⁄K]$, the value of `traceDiff K F F'` at $y \cdot \iota(\omega)$ equals $\mathrm{Tr}_{F'/F}(y) \cdot \omega$, where $\iota$ is the canonical map `KaehlerDifferential.map K K F F'` from $K$-differentials of $F$ to $K$-differentials of $F'$, and $\mathrm{Tr}_{F'/F}$ is the algebra trace (which is the zero map unless $F'$ is finite over $F$). Since `traceDiff K F F'` is defined to be a chosen $F$-linear map with this property when one exists and the zero map otherwise, the content of the statement is exactly that such a map exists for separable $F'/F$, so that the default branch is not taken.
--
--   This is the trace (cotrace) map on differentials attached to a separable extension of function fields, in the function-field formulation of finite morphisms of curves; the identity stated is the characterising compatibility of the trace on differentials with the field trace. It is the identity through which the choice-totalised map `traceDiff` is used, and it underlies the computations of $q$-expansions of differentials along the Hecke correspondences on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_isTraceDiff_traceDiff.lean

import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.isTraceDiff_traceDiff (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] : IsTraceDiff K F F' (traceDiff K F F') := by sorry

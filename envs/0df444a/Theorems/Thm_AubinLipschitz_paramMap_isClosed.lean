-- Prove2me | Theorems.Thm_AubinLipschitz_paramMap_isClosed
-- name    : AubinLipschitz.paramMap_isClosed
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:37.596599+00:00
-- url     : https://prove2.me/theorems/4ad0ca4b-92f3-4007-8392-06b71d74e5d0
-- title:
--   §5, p.34 — $F$ is a closed set-valued map (implicit in the paper)
-- statement:
--   Let $U$, $V$ be proper lower semicontinuous convex functions on finite-dimensional $X$, $Y$. The set-valued map $F$ of (9)–(10), with $G=\partial U$ and $H^{-1}=\partial V^*$, has closed graph: the set of all $(x,q,p,y,A)$ with $p\in\partial U(x)+A^*q$ and $y\in -Ax+\partial V^*(q)$ is closed in $X\times Y^*\times X^*\times Y\times L(X,Y)$.
--
--   The Inverse Function Theorem of §3 applies only to closed set-valued maps, so the proof of the goal needs this fact.
--
--   Differences from the source:
--   - reading: the paper never states this; it applies §3 Theorem 1, whose F is "a closed set-valued map", to F at p.34 → Lean states IsClosed of the graph of F; reason: the application at p.34 presupposes exactly this.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, p.34, "Hence Theorem 1 follows from the Inverse Function Theorem", with §3, Theorem 1, p.22

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_AubinLipschitz_graphOf
import Definitions.Def_AubinLipschitz_paramMap
import Definitions.Def_AubinLipschitz_subdiffConj
open RockafellarMaxMono.Shared

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, p.34, with §3, Theorem 1, p.22: the map `F` of (9)–(10) with `G = ∂U`,
`H⁻¹ = ∂V*` is a closed set-valued map, that is, its graph is closed. The paper uses this
without statement when it applies the Inverse Function Theorem. -/
theorem paramMap_isClosed {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (U : X → EReal) (V : Y → EReal) (hU : ProperConvex U) (hUlsc : LowerSemicontinuous U)
    (hV : ProperConvex V) (hVlsc : LowerSemicontinuous V) :
    IsClosed (graphOf (paramMap (subdiff U) (subdiffConj V))) := by sorry

end AubinLipschitz

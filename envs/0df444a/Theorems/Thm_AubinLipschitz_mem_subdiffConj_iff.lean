-- Prove2me | Theorems.Thm_AubinLipschitz_mem_subdiffConj_iff
-- name    : AubinLipschitz.mem_subdiffConj_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:22.495579+00:00
-- url     : https://prove2.me/theorems/9563664a-1445-422f-a7cd-c2b6cf3061c2
-- title:
--   §5, p.33 — $\partial V^*$ is the inverse of $\partial V$
-- statement:
--   Let $V:Y\to\mathbb R\cup\{+\infty\}$ be a proper lower semicontinuous convex function on a finite-dimensional space. For all $y\in Y$ and $q\in Y^*$,
--
--   $$
--   y\in\partial V^*(q)\iff q\in\partial V(y).
--   $$
--
--   In the paper's notation, with $H=\partial V$, this is $H^{-1}(q)=\partial V^*(q)$. It is what connects the inclusion (4)ii with the matrix of second derivatives.
--
--   Differences from the source: none.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, p.33, "H⁻¹(q) = ∂V*(q)"

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_AubinLipschitz_subdiffConj
open RockafellarMaxMono.Shared

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, p.33 ("`H⁻¹(q) = ∂V*(q)`"): for a proper lower semicontinuous convex function
`V` on a finite-dimensional space, `y ∈ ∂V*(q)` if and only if `q ∈ ∂V(y)`. -/
theorem mem_subdiffConj_iff {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (V : Y → EReal) (hV : ProperConvex V) (hVlsc : LowerSemicontinuous V)
    (y : Y) (q : StrongDual ℝ Y) : y ∈ subdiffConj V q ↔ q ∈ subdiff V y := by sorry

end AubinLipschitz

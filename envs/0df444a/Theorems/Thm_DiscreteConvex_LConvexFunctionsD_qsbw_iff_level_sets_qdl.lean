-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsD_qsbw_iff_level_sets_qdl
-- name    : DiscreteConvex.LConvexFunctionsD.qsbw_iff_level_sets_qdl
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T01:03:56.291754+00:00
-- url     : https://prove2.me/theorems/865687e9-8d5d-4be3-8df7-eb6a15443c64
-- title:
--   Theorem 7.51 -- qsbw_iff_level_sets_qdl
-- statement:
--   **Theorem 7.51** (p.200). A function $g:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ satisfies (QSBw) iff the level set $L(g,\alpha)$ satisfies (QDL) for every $\alpha\in\mathbb R$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.200, Theorem 7.51.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.200, Theorem 7.51

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_QSBw
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_QDL
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_LevelSet

namespace DiscreteConvex.LConvexFunctionsD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 7.51 (p.200). (QSBw) is equivalent to (QDL) of every level set. -/
theorem qsbw_iff_level_sets_qdl (g : (V → ℤ) → WithTop ℝ) :
    QSBw g ↔ ∀ alpha : ℝ, QDL (LevelSet g alpha) := by sorry

end DiscreteConvex.LConvexFunctionsD

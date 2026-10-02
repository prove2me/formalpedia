-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsE_qmw_iff_level_sets_qexcw
-- name    : DiscreteConvex.MConvexFunctionsE.qmw_iff_level_sets_qexcw
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:10:38.666986+00:00
-- url     : https://prove2.me/theorems/e44aeb65-6ca4-43e0-971f-f8d5284b2d9f
-- title:
--   Theorem 6.72 -- qmw_iff_level_sets_qexcw
-- statement:
--   **Theorem 6.72** (p.172). A function $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ satisfies (QMw) if and only if the level set $L(f,\alpha)$ satisfies (Q-EXCw) for all $\alpha\in\mathbb R$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.172, Theorem 6.72.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.172, Theorem 6.72

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QEXCw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_LevelSet

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.72 (p.172). (QMw) is equivalent to (Q-EXCw) of every level set. -/
theorem qmw_iff_level_sets_qexcw (f : (V → ℤ) → WithTop ℝ) :
    QMw f ↔ ∀ alpha : ℝ, QEXCw (LevelSet f alpha) := by sorry

end DiscreteConvex.MConvexFunctionsE

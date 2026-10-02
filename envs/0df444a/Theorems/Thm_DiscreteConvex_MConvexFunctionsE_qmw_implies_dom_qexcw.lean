-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsE_qmw_implies_dom_qexcw
-- name    : DiscreteConvex.MConvexFunctionsE.qmw_implies_dom_qexcw
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:11:12.776983+00:00
-- url     : https://prove2.me/theorems/f33d5922-a48e-421f-85d6-a9fed2a3fd32
-- title:
--   Proposition 6.73 -- qmw_implies_dom_qexcw
-- statement:
--   **Proposition 6.73** (p.172). If $f$ satisfies (QMw), then $\operatorname{dom} f$ satisfies (Q-EXCw).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.172, Proposition 6.73.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.172, Proposition 6.73

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QMw
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_QEXCw

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 6.73 (p.172). (QMw) implies (Q-EXCw) of the effective domain. -/
theorem qmw_implies_dom_qexcw (f : (V → ℤ) → WithTop ℝ) (hf : QMw f) : QEXCw (DomZ f) := by sorry

end DiscreteConvex.MConvexFunctionsE

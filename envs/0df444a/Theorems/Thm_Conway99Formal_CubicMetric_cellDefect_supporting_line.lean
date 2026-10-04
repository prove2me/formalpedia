-- Prove2me | Theorems.Thm_Conway99Formal_CubicMetric_cellDefect_supporting_line
-- name    : Conway99Formal.CubicMetric.cellDefect_supporting_line
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T04:06:23.618714+00:00
-- url     : https://prove2.me/theorems/d6f9e801-5bcf-4b3f-b133-e95124b6887c
-- title:
--   Linear supporting bound for the cell defect
-- statement:
--   For $p\in\{0,\ldots,12\}$ with $p<10$, $7(10-p)-19\le\operatorname{cellDefect}(p)$. The restriction $p<10$ is required.
-- source:
--   Exact original Lean source: formalization/2026-10-03/cubic-metric/Arithmetic.lean#136-139; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 cb5b20612f4683979bcf4f2a036ef30d4d5e2d3249e2bddfc63443bdcca909b4. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/cubic-metric/Arithmetic.lean#L136-L139.

import Definitions.Def_Arithmetic
import Mathlib

namespace Conway99Formal.CubicMetric
end Conway99Formal.CubicMetric

set_option autoImplicit false

open Conway99Formal.CubicMetric

theorem Conway99Formal.CubicMetric.cellDefect_supporting_line (p : Fin 13) (hp : p.val < 10) :
    7 * (10 - (p.val : ℤ)) - 19 ≤ cellDefect p.val := by sorry

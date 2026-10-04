-- Prove2me | Theorems.Thm_Conway99Formal_CubicMetric_cellDefect_pos_of_lt_ten
-- name    : Conway99Formal.CubicMetric.cellDefect_pos_of_lt_ten
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T04:06:17.589631+00:00
-- url     : https://prove2.me/theorems/b73efc3b-910c-4462-88a7-006e8e8d9bd2
-- title:
--   Cell defect is positive below ten
-- statement:
--   For $p\in\{0,\ldots,12\}$ with $p<10$, $0<\operatorname{cellDefect}(p)$. The range and strict bound are the premises.
-- source:
--   Exact original Lean source: formalization/2026-10-03/cubic-metric/Arithmetic.lean#131-134; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 cb5b20612f4683979bcf4f2a036ef30d4d5e2d3249e2bddfc63443bdcca909b4. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/cubic-metric/Arithmetic.lean#L131-L134.

import Definitions.Def_Arithmetic
import Mathlib

namespace Conway99Formal.CubicMetric
end Conway99Formal.CubicMetric

set_option autoImplicit false

open Conway99Formal.CubicMetric

theorem Conway99Formal.CubicMetric.cellDefect_pos_of_lt_ten (p : Fin 13) (hp : p.val < 10) :
    0 < cellDefect p.val := by sorry

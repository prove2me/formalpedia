-- Prove2me | Theorems.Thm_Conway99Formal_CubicMetric_cellDefect_table
-- name    : Conway99Formal.CubicMetric.cellDefect_table
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T04:06:36.882004+00:00
-- url     : https://prove2.me/theorems/f2434265-adc8-49d3-9ab5-3d0ee40bce91
-- title:
--   Exact cell-defect table
-- statement:
--   For each index $p$ in $\{0,\ldots,12\}$, `cellDefect(p)` equals the corresponding entry of $[60,50,40,31,23,16,10,6,3,1,0,0,0]$. This is a finite lookup identity.
-- source:
--   Exact original Lean source: formalization/2026-10-03/cubic-metric/Arithmetic.lean#117-121; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 cb5b20612f4683979bcf4f2a036ef30d4d5e2d3249e2bddfc63443bdcca909b4. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/cubic-metric/Arithmetic.lean#L117-L121.

import Definitions.Def_Arithmetic
import Mathlib

namespace Conway99Formal.CubicMetric
end Conway99Formal.CubicMetric

set_option autoImplicit false

open Conway99Formal.CubicMetric

theorem Conway99Formal.CubicMetric.cellDefect_table (p : Fin 13) :
    cellDefect p.val =
      ![60, 50, 40, 31, 23, 16, 10, 6, 3, 1, 0, 0, 0] p := by sorry

-- Prove2me | Theorems.Thm_Conway99Formal_CubicMetric_cellBound_table
-- name    : Conway99Formal.CubicMetric.cellBound_table
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T04:05:58.768342+00:00
-- url     : https://prove2.me/theorems/90463e7d-2d7e-4d1d-9c53-e7cd7be119cb
-- title:
--   Exact cell-bound table
-- statement:
--   For each index $p$ in $\{0,\ldots,12\}$, `cellBound(p)` equals the corresponding entry of $[879,735,595,471,359,255,171,115,79,51,35,35,39]$. This is a finite lookup identity.
-- source:
--   Exact original Lean source: formalization/2026-10-03/cubic-metric/Arithmetic.lean#111-115; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 cb5b20612f4683979bcf4f2a036ef30d4d5e2d3249e2bddfc63443bdcca909b4. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/cubic-metric/Arithmetic.lean#L111-L115.

import Definitions.Def_Arithmetic
import Mathlib

namespace Conway99Formal.CubicMetric
end Conway99Formal.CubicMetric

set_option autoImplicit false

open Conway99Formal.CubicMetric

theorem Conway99Formal.CubicMetric.cellBound_table (p : Fin 13) :
    cellBound p.val =
      ![879, 735, 595, 471, 359, 255, 171, 115, 79, 51, 35, 35, 39] p := by sorry

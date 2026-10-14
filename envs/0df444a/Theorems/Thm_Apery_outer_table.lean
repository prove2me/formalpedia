-- Prove2me | Theorems.Thm_Apery_outer_table
-- name    : Apery.outer_table
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T16:12:52.484327+00:00
-- url     : https://prove2.me/theorems/ff6e6bee-a5a7-4e69-88ba-ceb6df5b5bd4
-- title:
--   Outer table: $E_{\mathrm{out}}$ is affine on every piece of the grid on $[20/37, 3]$
-- statement:
--   For every $i < 13$ and $t_i \le x < t_{i+1}$ on the grid $20/37, 40/43, 1, 40/37, 3/2, 20/13, 60/37, 80/43, 2, 80/37, 5/2, 100/37, 120/43, 3$, the continuous outer profile equals the corresponding affine table piece: $E_{\mathrm{out}}(x) = g_{\mathrm{out},i}(x)$. This is `outer_table` of `Apery/Growth/OuterTable.lean`, the 13-piece piecewise-affine majorant used for the outer prime-sum estimate; the proof assembles the two halves `Apery.outer_table_lo`/`Apery.outer_table_hi`. **Formalization Note** `tOut`, `gOut`, `Eout` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/OuterTable.lean#L477-L531

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem outer_table : ∀ i < 13, ∀ x ∈ Set.Ico (tOut i) (tOut (i + 1)), Eout x = gOut i x := by
  sorry

end Apery

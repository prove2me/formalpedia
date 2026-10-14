-- Prove2me | Theorems.Thm_Apery_outer_table_11_12
-- name    : Apery.outer_table_11_12
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T17:09:36.916989+00:00
-- url     : https://prove2.me/theorems/817d3fcb-819b-4bd6-a1e5-0620a324ba97
-- title:
--   Outer table pieces 11-12: $E_{\mathrm{out}} = g_{\mathrm{out},i}$ on $t_i \le x < t_{i+1}$ (120/43 to 3)
-- statement:
--   On the pieces 11 to 12 of the outer grid $(120/43, 3)$, the continuous outer profile agrees with the corresponding affine table piece: $E_{\mathrm{out}}(x) = g_{\mathrm{out},i}(x)$ for $t_i \le x < t_{i+1}$. These are the generated lemmas `outPiece_11`...`outPiece_12` of `Apery/Growth/OuterTable.lean`, assembled as a block (the 13-piece table is split into small blocks for submission size). **Formalization Note** `tOut`, `gOut`, `Eout` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/OuterTable.lean

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem outer_table_11_12 : ∀ i, 11 ≤ i → i < 13 → ∀ x ∈ Set.Ico (tOut i) (tOut (i + 1)), Eout x = gOut i x := by
  sorry

end Apery

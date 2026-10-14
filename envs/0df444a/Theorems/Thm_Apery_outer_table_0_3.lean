-- Prove2me | Theorems.Thm_Apery_outer_table_0_3
-- name    : Apery.outer_table_0_3
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T17:09:52.941146+00:00
-- url     : https://prove2.me/theorems/832bbeb0-79a7-4d4b-b664-d5faa4e81ee9
-- title:
--   Outer table pieces 0-3: $E_{\mathrm{out}} = g_{\mathrm{out},i}$ on $t_i \le x < t_{i+1}$ (20/37 to 3/2)
-- statement:
--   On the pieces 0 to 3 of the outer grid $(20/37, 40/43, 1, 40/37, 3/2)$, the continuous outer profile agrees with the corresponding affine table piece: $E_{\mathrm{out}}(x) = g_{\mathrm{out},i}(x)$ for $t_i \le x < t_{i+1}$. These are the generated lemmas `outPiece_0`...`outPiece_3` of `Apery/Growth/OuterTable.lean`, assembled as a block (the 13-piece table is split into small blocks for submission size). **Formalization Note** `tOut`, `gOut`, `Eout` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/OuterTable.lean

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem outer_table_0_3 : ∀ i, 0 ≤ i → i < 4 → ∀ x ∈ Set.Ico (tOut i) (tOut (i + 1)), Eout x = gOut i x := by
  sorry

end Apery

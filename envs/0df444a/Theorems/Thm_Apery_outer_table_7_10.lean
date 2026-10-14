-- Prove2me | Theorems.Thm_Apery_outer_table_7_10
-- name    : Apery.outer_table_7_10
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T17:10:38.726918+00:00
-- url     : https://prove2.me/theorems/77b05e8e-eb13-4366-84a9-9cec34afb486
-- title:
--   Outer table pieces 7-10: $E_{\mathrm{out}} = g_{\mathrm{out},i}$ on $t_i \le x < t_{i+1}$ (2 to 100/37)
-- statement:
--   On the pieces 7 to 10 of the outer grid $(2, 80/37, 5/2, 100/37)$, the continuous outer profile agrees with the corresponding affine table piece: $E_{\mathrm{out}}(x) = g_{\mathrm{out},i}(x)$ for $t_i \le x < t_{i+1}$. These are the generated lemmas `outPiece_7`...`outPiece_10` of `Apery/Growth/OuterTable.lean`, assembled as a block (the 13-piece table is split into small blocks for submission size). **Formalization Note** `tOut`, `gOut`, `Eout` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/OuterTable.lean

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem outer_table_7_10 : ∀ i, 7 ≤ i → i < 11 → ∀ x ∈ Set.Ico (tOut i) (tOut (i + 1)), Eout x = gOut i x := by
  sorry

end Apery

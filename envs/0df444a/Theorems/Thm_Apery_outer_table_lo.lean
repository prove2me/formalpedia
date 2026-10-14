-- Prove2me | Theorems.Thm_Apery_outer_table_lo
-- name    : Apery.outer_table_lo
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T16:09:24.329737+00:00
-- url     : https://prove2.me/theorems/003b8aae-0f5f-4363-84ec-988ea60cea32
-- title:
--   Outer table on the first seven pieces ($20/37 \le x < 2$): $E_{\mathrm{out}} = g_{\mathrm{out},i}$
-- statement:
--   On each of the first seven pieces of the grid $20/37, 40/43, 1, 40/37, 3/2, 20/13, 60/37, 80/43$, the continuous outer profile agrees with the corresponding affine piece of the outer table: $E_{\mathrm{out}}(x) = g_{\mathrm{out},i}(x)$ for $t_i \le x < t_{i+1}$, $i \le 6$. These are the generated lemmas `outPiece_0`...`outPiece_6` of `Apery/Growth/OuterTable.lean`, assembled (the table is split in two for submission size). **Formalization Note** `tOut`, `gOut`, `Eout` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/OuterTable.lean#L12-L82

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

lemma outer_table_lo : ∀ i < 7, ∀ x ∈ Set.Ico (tOut i) (tOut (i + 1)), Eout x = gOut i x := by
  sorry

end Apery

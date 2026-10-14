-- Prove2me | Theorems.Thm_Apery_outer_table_hi
-- name    : Apery.outer_table_hi
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T16:09:03.841437+00:00
-- url     : https://prove2.me/theorems/8397487e-7efe-4e19-a4f5-d63c58a8bca6
-- title:
--   Outer table on the last six pieces ($2 \le x < 3$): $E_{\mathrm{out}} = g_{\mathrm{out},i}$
-- statement:
--   On each of the last six pieces of the grid $2, 80/37, 5/2, 100/37, 120/43, 3$, the continuous outer profile agrees with the corresponding affine piece of the outer table: $E_{\mathrm{out}}(x) = g_{\mathrm{out},i}(x)$ for $t_i \le x < t_{i+1}$, $7 \le i \le 12$. These are the generated lemmas `outPiece_7`...`outPiece_12` of `Apery/Growth/OuterTable.lean`, assembled (the table is split in two for submission size). **Formalization Note** `tOut`, `gOut`, `Eout` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/OuterTable.lean#L257-L466

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

lemma outer_table_hi : ∀ i, 7 ≤ i → i < 13 → ∀ x ∈ Set.Ico (tOut i) (tOut (i + 1)), Eout x = gOut i x := by
  sorry

end Apery

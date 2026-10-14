-- Prove2me | Theorems.Thm_Apery_outer_table_4_6
-- name    : Apery.outer_table_4_6
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T17:08:53.835445+00:00
-- url     : https://prove2.me/theorems/5ec85f8e-5f76-4fe2-b21e-2582ca45c805
-- title:
--   Outer table pieces 4-6: $E_{\mathrm{out}} = g_{\mathrm{out},i}$ on $t_i \le x < t_{i+1}$ (20/13 to 80/43)
-- statement:
--   On the pieces 4 to 6 of the outer grid $(20/13, 60/37, 80/43)$, the continuous outer profile agrees with the corresponding affine table piece: $E_{\mathrm{out}}(x) = g_{\mathrm{out},i}(x)$ for $t_i \le x < t_{i+1}$. These are the generated lemmas `outPiece_4`...`outPiece_6` of `Apery/Growth/OuterTable.lean`, assembled as a block (the 13-piece table is split into small blocks for submission size). **Formalization Note** `tOut`, `gOut`, `Eout` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/OuterTable.lean

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem outer_table_4_6 : ∀ i, 4 ≤ i → i < 7 → ∀ x ∈ Set.Ico (tOut i) (tOut (i + 1)), Eout x = gOut i x := by
  sorry

end Apery

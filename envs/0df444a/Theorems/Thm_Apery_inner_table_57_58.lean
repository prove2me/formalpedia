-- Prove2me | Theorems.Thm_Apery_inner_table_57_58
-- name    : Apery.inner_table_57_58
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T20:23:50.985221+00:00
-- url     : https://prove2.me/theorems/9465f38d-09ee-4144-b666-39843aef4ed9
-- title:
--   Inner table pieces 57-58: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ on $t_i \le x < t_{i+1}$
-- statement:
--   On the pieces 57 to 58 of the 125-piece inner grid on $[3, 20]$, the continuous inner profile agrees with the affine table: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ for $t_i \le x < t_{i+1}$. These are the generated lemmas `inPiece_57`...`inPiece_58` of `Apery/Growth/InnerTable.lean`, assembled as a block (the certificate is split into size-limited blocks for the platform compile budget). **Formalization Note** `tIn`, `kIn`, `gIn`, `Ein` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/InnerTable.lean

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem inner_table_57_58 : ∀ i, 57 ≤ i → i < 59 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  sorry

end Apery

-- Prove2me | Theorems.Thm_Apery_inner_table_81_83
-- name    : Apery.inner_table_81_83
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T21:00:41.33625+00:00
-- url     : https://prove2.me/theorems/fc35b36e-f4d1-40e5-b63e-315ec28db9b7
-- title:
--   Inner table pieces 81-83: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ on $t_i \le x < t_{i+1}$
-- statement:
--   On the pieces 81 to 83 of the 125-piece inner grid on $[3, 20]$, the continuous inner profile agrees with the affine table: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ for $t_i \le x < t_{i+1}$. These are the generated lemmas `inPiece_81`...`inPiece_83` of `Apery/Growth/InnerTable.lean`, assembled as a block (the certificate is split into size-limited blocks for the platform compile budget). **Formalization Note** `tIn`, `kIn`, `gIn`, `Ein` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/InnerTable.lean

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem inner_table_81_83 : ∀ i, 81 ≤ i → i < 84 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  sorry

end Apery

-- Prove2me | Theorems.Thm_Apery_inner_table_56_56
-- name    : Apery.inner_table_56_56
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T20:17:46.79799+00:00
-- url     : https://prove2.me/theorems/71271343-b222-4318-9280-c45f66a7d2dc
-- title:
--   Inner table pieces 56-56: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ on $t_i \le x < t_{i+1}$
-- statement:
--   On the pieces 56 to 56 of the 125-piece inner grid on $[3, 20]$, the continuous inner profile agrees with the affine table: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ for $t_i \le x < t_{i+1}$. These are the generated lemmas `inPiece_56`...`inPiece_56` of `Apery/Growth/InnerTable.lean`, assembled as a block (the certificate is split into size-limited blocks for the platform compile budget). **Formalization Note** `tIn`, `kIn`, `gIn`, `Ein` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/InnerTable.lean

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem inner_table_56_56 : ∀ i, 56 ≤ i → i < 57 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  sorry

end Apery

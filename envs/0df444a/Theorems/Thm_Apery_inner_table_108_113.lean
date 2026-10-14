-- Prove2me | Theorems.Thm_Apery_inner_table_108_113
-- name    : Apery.inner_table_108_113
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T17:46:36.551131+00:00
-- url     : https://prove2.me/theorems/6cdd67d3-9a24-4f2f-9723-0895d711d43a
-- title:
--   Inner table pieces 108-113: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ on $t_i \le x < t_{i+1}$
-- statement:
--   On the pieces 108 to 113 of the 125-piece inner grid on $[3, 20]$ (the zeros of the fractional parts $\{x\}$, $\{\alpha x\}$, $\{2\lambda x\}$, concatenated), the continuous inner profile agrees with the affine table: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ for $t_i \le x < t_{i+1}$. These are the generated lemmas `inPiece_108`...`inPiece_113` of `Apery/Growth/InnerTable.lean`, assembled as a block (the 125-piece certificate is split into size-limited blocks for the platform compile budget). **Formalization Note** `tIn`, `kIn`, `gIn`, `Ein` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/InnerTable.lean

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem inner_table_108_113 : ∀ i, 108 ≤ i → i < 114 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  sorry

end Apery

-- Prove2me | Theorems.Thm_Apery_inner_table_66_71
-- name    : Apery.inner_table_66_71
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T17:45:51.764987+00:00
-- url     : https://prove2.me/theorems/98ab07db-79ae-4b0f-b892-a950c0220e0c
-- title:
--   Inner table pieces 66-71: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ on $t_i \le x < t_{i+1}$
-- statement:
--   On the pieces 66 to 71 of the 125-piece inner grid on $[3, 20]$ (the zeros of the fractional parts $\{x\}$, $\{\alpha x\}$, $\{2\lambda x\}$, concatenated), the continuous inner profile agrees with the affine table: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ for $t_i \le x < t_{i+1}$. These are the generated lemmas `inPiece_66`...`inPiece_71` of `Apery/Growth/InnerTable.lean`, assembled as a block (the 125-piece certificate is split into size-limited blocks for the platform compile budget). **Formalization Note** `tIn`, `kIn`, `gIn`, `Ein` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/InnerTable.lean

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem inner_table_66_71 : ∀ i, 66 ≤ i → i < 72 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  sorry

end Apery

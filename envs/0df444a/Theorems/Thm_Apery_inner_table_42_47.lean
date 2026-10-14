-- Prove2me | Theorems.Thm_Apery_inner_table_42_47
-- name    : Apery.inner_table_42_47
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T17:45:51.795985+00:00
-- url     : https://prove2.me/theorems/48ffd872-508e-43a9-938f-bc771a6c24a5
-- title:
--   Inner table pieces 42-47: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ on $t_i \le x < t_{i+1}$
-- statement:
--   On the pieces 42 to 47 of the 125-piece inner grid on $[3, 20]$ (the zeros of the fractional parts $\{x\}$, $\{\alpha x\}$, $\{2\lambda x\}$, concatenated), the continuous inner profile agrees with the affine table: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ for $t_i \le x < t_{i+1}$. These are the generated lemmas `inPiece_42`...`inPiece_47` of `Apery/Growth/InnerTable.lean`, assembled as a block (the 125-piece certificate is split into size-limited blocks for the platform compile budget). **Formalization Note** `tIn`, `kIn`, `gIn`, `Ein` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/InnerTable.lean

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem inner_table_42_47 : ∀ i, 42 ≤ i → i < 48 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  sorry

end Apery

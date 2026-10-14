-- Prove2me | Theorems.Thm_Apery_inner_table_30_35
-- name    : Apery.inner_table_30_35
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T17:46:09.56285+00:00
-- url     : https://prove2.me/theorems/baa5d9f1-6a2e-4e04-ad7d-1652325e5bc5
-- title:
--   Inner table pieces 30-35: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ on $t_i \le x < t_{i+1}$
-- statement:
--   On the pieces 30 to 35 of the 125-piece inner grid on $[3, 20]$ (the zeros of the fractional parts $\{x\}$, $\{\alpha x\}$, $\{2\lambda x\}$, concatenated), the continuous inner profile agrees with the affine table: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ for $t_i \le x < t_{i+1}$. These are the generated lemmas `inPiece_30`...`inPiece_35` of `Apery/Growth/InnerTable.lean`, assembled as a block (the 125-piece certificate is split into size-limited blocks for the platform compile budget). **Formalization Note** `tIn`, `kIn`, `gIn`, `Ein` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/InnerTable.lean

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem inner_table_30_35 : ∀ i, 30 ≤ i → i < 36 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  sorry

end Apery

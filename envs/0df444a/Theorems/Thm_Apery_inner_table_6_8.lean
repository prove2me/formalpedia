-- Prove2me | Theorems.Thm_Apery_inner_table_6_8
-- name    : Apery.inner_table_6_8
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T18:42:21.243355+00:00
-- url     : https://prove2.me/theorems/4046338e-c69c-48c0-94d4-ec87393d7473
-- title:
--   Inner table pieces 6-8: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ on $t_i \le x < t_{i+1}$
-- statement:
--   On the pieces 6 to 8 of the 125-piece inner grid on $[3, 20]$, the continuous inner profile agrees with the affine table: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ for $t_i \le x < t_{i+1}$. These are the generated lemmas `inPiece_6`...`inPiece_8` of `Apery/Growth/InnerTable.lean`, assembled as a block (the certificate is split into size-limited blocks for the platform compile budget). **Formalization Note** `tIn`, `kIn`, `gIn`, `Ein` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/InnerTable.lean

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem inner_table_6_8 : ∀ i, 6 ≤ i → i < 9 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  sorry

end Apery

-- Prove2me | Theorems.Thm_Apery_inner_table
-- name    : Apery.inner_table
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T17:45:56.606596+00:00
-- url     : https://prove2.me/theorems/f9f63382-727e-4c5f-bc7c-00c76de2015b
-- title:
--   Inner table: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$ on every piece of the 125-piece grid on $[3,20]$
-- statement:
--   For every $i < 125$ and $t_i \le x < t_{i+1}$ on the 125-piece inner grid on $[3,20]$, the continuous inner profile equals the corresponding affine table piece: $E_{\mathrm{in}}(x, k_i) = g_{\mathrm{in},i}(x)$. This is `inner_table` of `Apery/Growth/InnerSum.lean`, the piecewise-affine majorant used in the inner prime-sum estimate; the proof assembles the size-split blocks `Apery.inner_table_a_b`. **Formalization Note** `tIn`, `kIn`, `gIn`, `Ein` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/InnerSum.lean#L25-L528

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem inner_table : ∀ i < 125, ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), Ein x (kIn i) = gIn i x := by
  sorry

end Apery

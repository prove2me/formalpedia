-- Prove2me | Theorems.Thm_Apery_inner_table_k_0_30
-- name    : Apery.inner_table_k_0_30
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T17:46:00.565547+00:00
-- url     : https://prove2.me/theorems/bd5de0dc-507c-41e2-baf9-7f8a862a134d
-- title:
--   Inner table k-ranges, pieces 0-30: $-2\lfloor x\rfloor - 6 \le k_i \le 8\lfloor x\rfloor + 20$
-- statement:
--   For every piece 0 to 30 of the inner table and $t_i \le x < t_{i+1}$, the table exponent $k_i$ satisfies $-2\lfloor x\rfloor - 6 \le k_i \le 8\lfloor x\rfloor + 20$, i.e. $k_i$ lies in the admissible level window of the inner bound at $x = K/p$. This is a block of `inner_table_k` of `Apery/Growth/InnerSum.lean` (split for the platform compile budget). **Formalization Note** `tIn`, `kIn` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/InnerSum.lean#L529-L1034

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem inner_table_k_0_30 : ∀ i, 0 ≤ i → i ≤ 30 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), -2 * (⌊x⌋₊ : ℤ) - 6 ≤ kIn i ∧ kIn i ≤ 8 * (⌊x⌋₊ : ℤ) + 20 := by
  sorry

end Apery

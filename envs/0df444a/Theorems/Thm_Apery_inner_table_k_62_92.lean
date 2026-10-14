-- Prove2me | Theorems.Thm_Apery_inner_table_k_62_92
-- name    : Apery.inner_table_k_62_92
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T17:46:10.380628+00:00
-- url     : https://prove2.me/theorems/c23ad629-3dc3-48aa-9d45-7e82d640b64e
-- title:
--   Inner table k-ranges, pieces 62-92: $-2\lfloor x\rfloor - 6 \le k_i \le 8\lfloor x\rfloor + 20$
-- statement:
--   For every piece 62 to 92 of the inner table and $t_i \le x < t_{i+1}$, the table exponent $k_i$ satisfies $-2\lfloor x\rfloor - 6 \le k_i \le 8\lfloor x\rfloor + 20$, i.e. $k_i$ lies in the admissible level window of the inner bound at $x = K/p$. This is a block of `inner_table_k` of `Apery/Growth/InnerSum.lean` (split for the platform compile budget). **Formalization Note** `tIn`, `kIn` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/InnerSum.lean#L529-L1034

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem inner_table_k_62_92 : ∀ i, 62 ≤ i → i ≤ 92 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), -2 * (⌊x⌋₊ : ℤ) - 6 ≤ kIn i ∧ kIn i ≤ 8 * (⌊x⌋₊ : ℤ) + 20 := by
  sorry

end Apery

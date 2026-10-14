-- Prove2me | Theorems.Thm_Apery_inner_table_k_93_124
-- name    : Apery.inner_table_k_93_124
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T17:46:12.941904+00:00
-- url     : https://prove2.me/theorems/65287629-7ee3-44e7-b0d5-9cfad61af901
-- title:
--   Inner table k-ranges, pieces 93-124: $-2\lfloor x\rfloor - 6 \le k_i \le 8\lfloor x\rfloor + 20$
-- statement:
--   For every piece 93 to 124 of the inner table and $t_i \le x < t_{i+1}$, the table exponent $k_i$ satisfies $-2\lfloor x\rfloor - 6 \le k_i \le 8\lfloor x\rfloor + 20$, i.e. $k_i$ lies in the admissible level window of the inner bound at $x = K/p$. This is a block of `inner_table_k` of `Apery/Growth/InnerSum.lean` (split for the platform compile budget). **Formalization Note** `tIn`, `kIn` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/InnerSum.lean#L529-L1034

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem inner_table_k_93_124 : ∀ i, 93 ≤ i → i ≤ 124 → ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)), -2 * (⌊x⌋₊ : ℤ) - 6 ≤ kIn i ∧ kIn i ≤ 8 * (⌊x⌋₊ : ℤ) + 20 := by
  sorry

end Apery

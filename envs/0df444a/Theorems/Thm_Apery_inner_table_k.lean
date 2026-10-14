-- Prove2me | Theorems.Thm_Apery_inner_table_k
-- name    : Apery.inner_table_k
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T17:46:02.516458+00:00
-- url     : https://prove2.me/theorems/1c3c5796-2091-48c0-86f4-aa6c9cb96905
-- title:
--   Inner table k-ranges: $-2\lfloor x\rfloor - 6 \le k_i \le 8\lfloor x\rfloor + 20$ on every piece
-- statement:
--   For every $i < 125$ and $t_i \le x < t_{i+1}$ on the inner grid, the table exponent $k_i$ satisfies $-2\lfloor x\rfloor - 6 \le k_i \le 8\lfloor x\rfloor + 20$, i.e. $k_i$ lies in the admissible level window of the inner bound at $x = K/p$. This is `inner_table_k` of `Apery/Growth/InnerSum.lean`; the proof assembles the size-split blocks `Apery.inner_table_k_a_b`. **Formalization Note** `tIn`, `kIn` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/InnerSum.lean#L529-L1034

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem inner_table_k : ∀ i < 125, ∀ x ∈ Set.Ico (tIn i) (tIn (i + 1)),
    -2 * (⌊x⌋₊ : ℤ) - 6 ≤ kIn i ∧ kIn i ≤ 8 * (⌊x⌋₊ : ℤ) + 20 := by
  sorry

end Apery

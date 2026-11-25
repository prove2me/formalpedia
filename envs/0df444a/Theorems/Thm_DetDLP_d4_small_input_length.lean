-- Prove2me | Theorems.Thm_DetDLP_d4_small_input_length
-- name    : DetDLP.d4_small_input_length
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T06:07:39.440194+00:00
-- url     : https://prove2.me/theorems/20acc2da-f3e4-4ac8-a1fe-3e026709e6d2
-- title:
--   Length of a bounded-core terminal instance
-- statement:
--   Below a fixed core logarithm threshold, the entire terminal input word has length polynomial in the core size plus the descriptor length. This includes the graph, lookup indicator, size fields, and every endpoint record.

import Definitions.Def_DetDLP_D4Plan
open DetDLP DetDLP.D4Plan
set_option autoImplicit false

theorem DetDLP.d4_small_input_length (C c L : ℕ) (hc : 0 < c) : ∃ K : ℕ,
  ∀ x : Input C c, Nat.clog 2 x.S < L → (input x).length ≤ K * (size x + 1)^K := by sorry

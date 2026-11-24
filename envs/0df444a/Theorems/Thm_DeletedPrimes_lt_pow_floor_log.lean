-- Prove2me | Theorems.Thm_DeletedPrimes_lt_pow_floor_log
-- name    : DeletedPrimes.lt_pow_floor_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:06:31.152815+00:00
-- url     : https://prove2.me/theorems/eb49925c-fb38-4fc2-b5cb-9a99759a41f6
-- title:
--   Deleted Primes: lt pow floor log
-- statement:
--   `N < Y^{⌊log N / log Y⌋ + 1}` for `N ≥ 1`, `Y ≥ 2`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L43-L55
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L43-L55

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity
set_option autoImplicit false
open Real
open DeletedPrimes
open Classical

theorem DeletedPrimes.lt_pow_floor_log {N Y : ℕ} (hN : 1 ≤ N) (hY : 2 ≤ Y) :
    N < Y ^ (⌊Real.log N / Real.log Y⌋₊ + 1) := by sorry

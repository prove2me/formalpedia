-- Prove2me | Theorems.Thm_DeletedPrimes_card_window_dvd_le
-- name    : DeletedPrimes.card_window_dvd_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:55:32.192285+00:00
-- url     : https://prove2.me/theorems/a342aa4f-138a-4947-a318-bef174eaf9f0
-- title:
--   Deleted Primes: card window dvd le
-- statement:
--   The integers `j ∈ [-J, J]` with `q ∣ n + j` number at most `2J/q + 1`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L79-L112
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L79-L112

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity
set_option autoImplicit false
open Real
open DeletedPrimes
open Classical

theorem DeletedPrimes.card_window_dvd_le (n : ℤ) (J q : ℕ) (hq : 0 < q) :
    ((Finset.Icc (-(J : ℤ)) J).filter (fun j => (q : ℤ) ∣ n + j)).card ≤ 2 * J / q + 1 := by sorry

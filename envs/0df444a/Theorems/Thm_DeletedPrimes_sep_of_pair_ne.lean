-- Prove2me | Theorems.Thm_DeletedPrimes_sep_of_pair_ne
-- name    : DeletedPrimes.sep_of_pair_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:08:09.15081+00:00
-- url     : https://prove2.me/theorems/178682ac-0b5d-470d-b218-2cfecfc47606
-- title:
--   Deleted Primes: sep of pair ne
-- statement:
--   Step 6: distinct pairs `(q, m) ≠ (q', m')`, `m, m' = ±1`, give fractions at distance `≥ 1/(qq')`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L252-L267
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L252-L267

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity
set_option autoImplicit false
open Real
open DeletedPrimes
open Classical

theorem DeletedPrimes.sep_of_pair_ne {q q' : ℕ} {m m' : ℤ} (hq : 0 < q) (hq' : 0 < q') (hm : m = 1 ∨ m = -1)
    (hm' : m' = 1 ∨ m' = -1) (hne : (q, m) ≠ (q', m')) :
    1 / ((q : ℝ) * q') ≤ |(m : ℝ) / q - (m' : ℝ) / q'| := by sorry

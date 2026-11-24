-- Prove2me | Theorems.Thm_DeletedPrimes_sep_of_ne
-- name    : DeletedPrimes.sep_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:07:52.305907+00:00
-- url     : https://prove2.me/theorems/510f72c8-5513-40da-92c1-d5868b7cfdf0
-- title:
--   Deleted Primes: sep of ne
-- statement:
--   Steps 3 and 4: a non-resonant pair is `1/(dq)`-separated.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L239-L249
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L239-L249

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity
set_option autoImplicit false
open Real
open DeletedPrimes
open Classical

theorem DeletedPrimes.sep_of_ne {k d q m : ℤ} (hd : 0 < d) (hq : 0 < q) (h : k * q ≠ m * d) :
    1 / ((d : ℝ) * q) ≤ |(k : ℝ) / d - (m : ℝ) / q| := by sorry

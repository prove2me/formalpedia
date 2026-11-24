-- Prove2me | Theorems.Thm_DeletedPrimes_near_witness
-- name    : DeletedPrimes.near_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:08:19.121809+00:00
-- url     : https://prove2.me/theorems/9d531050-9108-4bca-80e7-7397169d7111
-- title:
--   Deleted Primes: near witness
-- statement:
--   Lemma 5.1: if `q ∤ a`, then `j = kq − a` is a nonzero witness with `q ∣ a + j`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L284-L290
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L284-L290

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity
set_option autoImplicit false
open Real
open DeletedPrimes
open Classical

theorem DeletedPrimes.near_witness {q k a : ℤ} (ha : ¬ q ∣ a) : k * q - a ≠ 0 ∧ q ∣ a + (k * q - a) := by sorry

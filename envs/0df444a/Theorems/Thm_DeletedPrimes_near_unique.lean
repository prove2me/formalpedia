-- Prove2me | Theorems.Thm_DeletedPrimes_near_unique
-- name    : DeletedPrimes.near_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:08:10.918385+00:00
-- url     : https://prove2.me/theorems/e42ebda8-0cf7-4679-b67e-658c9892a388
-- title:
--   Deleted Primes: near unique
-- statement:
--   Lemma 5.1: at most one `k` has `|kq − a| < q/2`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L270-L281
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L270-L281

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity
set_option autoImplicit false
open Real
open DeletedPrimes
open Classical

theorem DeletedPrimes.near_unique {q k k' a : ℤ} (hq : 0 < q) (hk : 2 * |k * q - a| < q)
    (hk' : 2 * |k' * q - a| < q) : k = k' := by sorry

-- Prove2me | Theorems.Thm_DeletedPrimes_card_primes_dvd_le
-- name    : DeletedPrimes.card_primes_dvd_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:55:09.197603+00:00
-- url     : https://prove2.me/theorems/222f533a-0a44-4cd0-baea-3979a0a7b501
-- title:
--   Deleted Primes: card primes dvd le
-- statement:
--   A nonzero integer `N` with `|N| < Y^{L+1}` (`Y ≥ 2`) is divisible by at most `L` primes `≥ Y` of a finset.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L27-L40
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L27-L40

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity
set_option autoImplicit false
open Real
open DeletedPrimes
open Classical

theorem DeletedPrimes.card_primes_dvd_le {T : Finset ℕ} {Y L : ℕ} {N : ℤ} (hY2 : 2 ≤ Y) (hN : N ≠ 0)
    (hNb : N.natAbs < Y ^ (L + 1)) (hp : ∀ q ∈ T, q.Prime) (hY : ∀ q ∈ T, Y ≤ q)
    (hd : ∀ q ∈ T, (q : ℤ) ∣ N) : T.card ≤ L := by sorry

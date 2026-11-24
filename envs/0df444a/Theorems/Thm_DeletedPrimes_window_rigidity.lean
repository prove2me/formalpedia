-- Prove2me | Theorems.Thm_DeletedPrimes_window_rigidity
-- name    : DeletedPrimes.window_rigidity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:07:45.231828+00:00
-- url     : https://prove2.me/theorems/2be9dd80-ecfa-44ca-9d13-bb5934a1b168
-- title:
--   Deleted Primes: window rigidity
-- statement:
--   **Lemma 5.2 (composite window rigidity).**
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L115-L230
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L115-L230

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity
set_option autoImplicit false
open Real
open DeletedPrimes
open Classical

theorem DeletedPrimes.window_rigidity {k : ℕ} (T : Fin k → Finset ℕ) (Y L : Fin k → ℕ)
    (hp : ∀ i, ∀ q ∈ T i, q.Prime) (hY : ∀ i, ∀ q ∈ T i, Y i ≤ q) (hY2 : ∀ i, 2 ≤ Y i)
    (n : ℤ) (J : ℕ) (hnJ : (J : ℤ) < |n|)
    (hL : ∀ i, ∀ j : ℤ, |j| ≤ J → (n + j).natAbs < Y i ^ (L i + 1)) (I : Finset (Fin k)) :
    ((Fintype.piFinset T).filter
        fun f : Fin k → ℕ => ∃ j : ℤ, j ≠ 0 ∧ |j| ≤ J ∧ ((∏ i, f i : ℕ) : ℤ) ∣ n + j).card
      ≤ (∏ i ∈ I, (T i).card) * (2 * J / ∏ i ∈ I, Y i + 1) * ∏ i ∈ Iᶜ, L i := by sorry

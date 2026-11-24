-- Prove2me | Theorems.Thm_DeletedPrimes_prod_injOn
-- name    : DeletedPrimes.prod_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:06:50.949703+00:00
-- url     : https://prove2.me/theorems/2b38a171-1907-4927-8c46-5a61cf10067f
-- title:
--   Deleted Primes: prod inj On
-- statement:
--   The product map `f ↦ ∏ f i` is injective on `∏ T_i` when the `T_i` are pairwise disjoint sets of primes.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L58-L76
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Rigidity.lean#L58-L76

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity
set_option autoImplicit false
open Real
open DeletedPrimes
open Classical

theorem DeletedPrimes.prod_injOn {k : ℕ} (T : Fin k → Finset ℕ) (hp : ∀ i, ∀ q ∈ T i, q.Prime)
    (hdisj : Pairwise fun i i' => Disjoint (T i) (T i')) :
    Set.InjOn (fun f : Fin k → ℕ => ∏ i, f i) (Fintype.piFinset T : Set (Fin k → ℕ)) := by sorry

-- Prove2me | Theorems.Thm_DeletedPrimes_abs_saw_le
-- name    : DeletedPrimes.abs_saw_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:52:55.31261+00:00
-- url     : https://prove2.me/theorems/289a34d0-7908-4ddd-8e38-18811b93ab5e
-- title:
--   Deleted Primes: abs saw le
-- statement:
--   The Deleted Primes construction uses the abs saw le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L373-L377
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L373-L377

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.abs_saw_le (u : ℝ) : |saw u| ≤ 1 / 2 := by sorry

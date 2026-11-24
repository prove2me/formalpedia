-- Prove2me | Theorems.Thm_DeletedPrimes_moment_exponent
-- name    : DeletedPrimes.moment_exponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:57:06.080829+00:00
-- url     : https://prove2.me/theorems/c2825566-f818-4888-af13-346bf5bacf59
-- title:
--   Deleted Primes: moment exponent
-- statement:
--   Proposition 7.2: `α − 1 − 2b < −1 ↔ α/2 < b`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L32-L33
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L32-L33

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.moment_exponent {α b : ℝ} : α - 1 - 2 * b < -1 ↔ α / 2 < b := by sorry

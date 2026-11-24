-- Prove2me | Theorems.Thm_DeletedPrimes_density_eq_tprod
-- name    : DeletedPrimes.density_eq_tprod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:59:55.561722+00:00
-- url     : https://prove2.me/theorems/40bb3661-e982-48da-bacf-910c13412368
-- title:
--   Deleted Primes: density eq tprod
-- statement:
--   `a_S = ∏_{p ∈ S}(1 − 1/p)`, as a product over all primes.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L288-L309
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L288-L309

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.density_eq_tprod
    (h1 : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-1 : ℝ))) :
    density S = ∏' p : Nat.Primes, (if (p : ℕ) ∈ S then 1 - 1 / (p : ℝ) else 1) := by sorry

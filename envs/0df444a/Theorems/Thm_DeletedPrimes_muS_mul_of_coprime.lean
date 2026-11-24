-- Prove2me | Theorems.Thm_DeletedPrimes_muS_mul_of_coprime
-- name    : DeletedPrimes.muS_mul_of_coprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:51:36.62164+00:00
-- url     : https://prove2.me/theorems/ab732b57-363d-4b5d-9074-31a3d7affe85
-- title:
--   Deleted Primes: mu S mul of coprime
-- statement:
--   Step 5 of §5: `μ_S(qd') = μ_S(q) μ_S(d')` for coprime `q, d'`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L172-L173
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L172-L173

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.muS_mul_of_coprime {q d : ℕ} (h : Nat.Coprime q d) : muS S (q * d) = muS S q * muS S d := by sorry

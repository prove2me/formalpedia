-- Prove2me | Theorems.Thm_DeletedPrimes_hitExp_perturb
-- name    : DeletedPrimes.hitExp_perturb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:04:29.748052+00:00
-- url     : https://prove2.me/theorems/aaed2071-baae-40e4-8938-de27c6553f57
-- title:
--   Deleted Primes: hit Exp perturb
-- statement:
--   Unequal block weights `s_i` (the exponent share of `i` blocks) with `|s_i − i/k| ≤ δ` change the hit exponent by
--   at most `(1+α)κδ`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L344-L371
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L344-L371

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.hitExp_perturb {k : ℕ} {α κ τ δ : ℝ} (h0 : 0 ≤ α) (hκ : 0 ≤ κ) (s : ℕ → ℝ)
    (hs : ∀ i ≤ k, |s i - i / k| ≤ δ) :
    (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one
        (fun i => α * κ * s i + max (κ - τ - κ * s i) 0)
      ≤ hitExp k α κ τ + (1 + α) * κ * δ := by sorry

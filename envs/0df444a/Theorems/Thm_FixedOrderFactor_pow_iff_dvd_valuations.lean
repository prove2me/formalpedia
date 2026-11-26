-- Prove2me | Theorems.Thm_FixedOrderFactor_pow_iff_dvd_valuations
-- name    : FixedOrderFactor.pow_iff_dvd_valuations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:55:31.817802+00:00
-- url     : https://prove2.me/theorems/069d94de-5fd0-41a2-9ab4-35af2cc30be7
-- title:
--   Fixed Order Factor: pow iff dvd valuations
-- statement:
--   `m/n` is an `r`-th power in `ℚ` exactly when `r` divides every `v_q(m) - v_q(n)`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L75-L100
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L75-L100

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
public import Definitions.Def_FixedOrderFactor_ModelPairs
set_option autoImplicit true
@[expose] public section
public section
open Finset Complex
open FixedOrderFactor

theorem FixedOrderFactor.pow_iff_dvd_valuations {r : ℕ} (hr : 0 < r) {S : Finset Nat.Primes} {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hS : ∀ q : Nat.Primes, (q : ℕ) ∣ m * n → q ∈ S) :
    (∃ x : ℚ, (m : ℚ) / n = x ^ r) ↔
      ∀ q ∈ S, (r : ℤ) ∣ (m.factorization q : ℤ) - n.factorization q := by sorry

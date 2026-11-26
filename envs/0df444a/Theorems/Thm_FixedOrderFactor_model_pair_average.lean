-- Prove2me | Theorems.Thm_FixedOrderFactor_model_pair_average
-- name    : FixedOrderFactor.model_pair_average
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:06:44.382248+00:00
-- url     : https://prove2.me/theorems/85866d00-5ac9-5ccb-bed0-c77133c19955
-- title:
--   Fixed Order Factor: model pair average
-- statement:
--   **The model keeps exactly the `r`-th power ratios.** If `z_q` are independent and uniform on
--   the `r`-th roots of unity, then `E[z^m conj(z^n)]` is `1` when `m/n` is the `r`-th power of a
--   rational number and `0` otherwise (for `m, n ≥ 1` whose prime factors lie in `S`).
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L159-L163
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L159-L163

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
open Classical

theorem FixedOrderFactor.model_pair_average {r : ℕ} (hr : 0 < r) (S : Finset Nat.Primes) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hS : ∀ q : Nat.Primes, (q : ℕ) ∣ m * n → q ∈ S) :
    (1 / (r : ℂ) ^ S.card) * ∑ j : S → Fin r, zPow r S j m * starRingEnd ℂ (zPow r S j n) =
      if ∃ x : ℚ, (m : ℚ) / n = x ^ r then 1 else 0 := by sorry

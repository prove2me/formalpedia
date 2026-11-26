-- Prove2me | Theorems.Thm_FixedOrderFactor_div_eq_pow_iff
-- name    : FixedOrderFactor.div_eq_pow_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:06:44.611333+00:00
-- url     : https://prove2.me/theorems/66481f54-7bef-59cd-9ab7-419c67c9e1ce
-- title:
--   Fixed Order Factor: div eq pow iff
-- statement:
--   **The surviving pairs.** For positive integers `m, n`, the quotient `m/n` is the `r`-th power
--   of a rational number exactly when `m = d aʳ` and `n = d bʳ` with `a, b` coprime.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L150-L153
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L150-L153

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.div_eq_pow_iff {r m n : ℕ} (hr : 0 < r) (hm : 0 < m) (hn : 0 < n) :
    (∃ q : ℚ, (m : ℚ) / n = q ^ r) ↔
      ∃ d a b : ℕ, 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ m = d * a ^ r ∧ n = d * b ^ r := by sorry

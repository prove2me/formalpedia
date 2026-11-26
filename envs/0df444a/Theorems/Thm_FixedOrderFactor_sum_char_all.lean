-- Prove2me | Theorems.Thm_FixedOrderFactor_sum_char_all
-- name    : FixedOrderFactor.sum_char_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:06:44.920055+00:00
-- url     : https://prove2.me/theorems/3bc691c3-385f-40c0-ab85-cb98a6f4c631
-- title:
--   Fixed Order Factor: sum char all
-- statement:
--   The full family, for contrast: summed over all characters modulo `p`, `χ(m) conj χ(n)`
--   vanishes for distinct `m, n` below `p`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L143-L146
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L143-L146

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.sum_char_all (p : ℕ) [Fact p.Prime] {m n : ℕ} (hmn : m ≠ n) (hm : m < p) (hn : n < p)
    (hn0 : n ≠ 0) :
    ∑ χ : DirichletCharacter ℂ p, χ m * starRingEnd ℂ (χ n) = 0 := by sorry

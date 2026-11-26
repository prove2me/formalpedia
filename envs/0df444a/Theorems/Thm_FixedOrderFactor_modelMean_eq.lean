-- Prove2me | Theorems.Thm_FixedOrderFactor_modelMean_eq
-- name    : FixedOrderFactor.modelMean_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:05:38.316263+00:00
-- url     : https://prove2.me/theorems/5d19c570-959d-4b18-a7d0-d53814fd7de4
-- title:
--   Fixed Order Factor: model Mean eq
-- statement:
--   **Random Euler product model, finite form.**
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L32-L34
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L32-L34

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.modelMean_eq (r : ℕ) (S : Finset Nat.Primes) :
    modelMean r S = ∏ q ∈ S, muAvg r (1 / (q : ℝ)) := by sorry

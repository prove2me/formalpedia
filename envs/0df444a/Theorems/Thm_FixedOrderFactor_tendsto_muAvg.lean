-- Prove2me | Theorems.Thm_FixedOrderFactor_tendsto_muAvg
-- name    : FixedOrderFactor.tendsto_muAvg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:05:23.51281+00:00
-- url     : https://prove2.me/theorems/28d554b9-76ee-46d0-b8c0-8704969654d5
-- title:
--   Fixed Order Factor: tendsto mu Avg
-- statement:
--   The full-circle factor is the limit of the order-`r` factor.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L27-L29
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L27-L29

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.tendsto_muAvg {x : ℝ} (hx : |x| < 1) :
    Tendsto (fun r => muAvg r x) atTop (𝓝 (1 / (1 - x ^ 2))) := by sorry

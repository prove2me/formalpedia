-- Prove2me | Theorems.Thm_FixedOrderFactor_sum_orbitAvg_eq_zero
-- name    : FixedOrderFactor.sum_orbitAvg_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:07:10.63796+00:00
-- url     : https://prove2.me/theorems/9a0be186-3e10-5de9-a45f-49b85c62e53d
-- title:
--   Fixed Order Factor: sum orbit Avg eq zero
-- statement:
--   The class function has mean zero: `∑_{t<s} ϱ_s(t) = 0` for `s > 1`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L172-L173
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L172-L173

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.sum_orbitAvg_eq_zero {s : ℕ} (hs : 1 < s) : ∑ t ∈ Finset.range s, orbitAvg s t = 0 := by sorry

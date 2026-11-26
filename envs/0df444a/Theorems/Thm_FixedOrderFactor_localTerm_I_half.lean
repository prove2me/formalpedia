-- Prove2me | Theorems.Thm_FixedOrderFactor_localTerm_I_half
-- name    : FixedOrderFactor.localTerm_I_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:06:17.260815+00:00
-- url     : https://prove2.me/theorems/02446429-c74c-543f-aa8b-0c7a768f0188
-- title:
--   Fixed Order Factor: local Term I half
-- statement:
--   The forced factor at `2`: `|1 ∓ i/2|⁻² = 4/5`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L94-L96
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L94-L96

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.localTerm_I_half : localTerm Complex.I (1 / 2) = 4 / 5 ∧
    localTerm (-Complex.I) (1 / 2) = 4 / 5 := by sorry

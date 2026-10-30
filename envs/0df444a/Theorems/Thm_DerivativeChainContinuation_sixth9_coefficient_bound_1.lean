-- Prove2me | Theorems.Thm_DerivativeChainContinuation_sixth9_coefficient_bound_1
-- name    : DerivativeChainContinuation.sixth9_coefficient_bound_1
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T04:31:47.732251+00:00
-- url     : https://prove2.me/theorems/f63e5710-02f2-49fe-ac28-39904f5cd1dc
-- title:
--   Uniform bound for Newton coefficient C1 on the closed disk of radius two
-- statement:
--   Let $C_1:\mathbb C\to\mathbb C$ be the exact rational-coefficient polynomial `sixth9C1` in the imported definition bundle. Every $t\in\mathbb C$ with $|t|\le2$ satisfies
--
--   $$
--   |C_1(t)|\le 10^{-5}.
--   $$
--
--   This uniform closed-disk estimate bounds the linear coefficient of the shifted Newton map. The coefficient table and the stated rational bound are exact.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Sixth9Bound1.lean#L8-L10

import Mathlib
import Definitions.Def_DerivativeChainContinuation_Sixth9C1Data
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators

theorem DerivativeChainContinuation.sixth9_coefficient_bound_1 (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖sixth9C1 t‖ ≤ 1/100000 := by sorry

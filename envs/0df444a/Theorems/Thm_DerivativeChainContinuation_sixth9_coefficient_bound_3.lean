-- Prove2me | Theorems.Thm_DerivativeChainContinuation_sixth9_coefficient_bound_3
-- name    : DerivativeChainContinuation.sixth9_coefficient_bound_3
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T04:36:59.276509+00:00
-- url     : https://prove2.me/theorems/33e671a0-ee21-4850-87f2-1e9d05a3e15c
-- title:
--   Uniform bound for Newton coefficient C3 on the closed disk of radius two
-- statement:
--   Let $C_3:\mathbb C\to\mathbb C$ be the exact rational-coefficient polynomial `sixth9C3` in the imported definition bundle. Every $t\in\mathbb C$ with $|t|\le2$ satisfies
--
--   $$
--   |C_3(t)|\le 1.
--   $$
--
--   This uniform closed-disk estimate bounds the cubic coefficient of the shifted Newton map. The coefficient table and the stated rational bound are exact.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/Sixth9Bound3.lean#L8-L10

import Mathlib
import Definitions.Def_DerivativeChainContinuation_Sixth9C3Data
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

theorem DerivativeChainContinuation.sixth9_coefficient_bound_3 (t : ℂ) (ht : ‖t‖ ≤ 2) : ‖sixth9C3 t‖ ≤ 1 := by sorry

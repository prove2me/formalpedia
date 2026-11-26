-- Prove2me | Theorems.Thm_Erdos266_quad_dom
-- name    : Erdos266.quad_dom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:40:36.883372+00:00
-- url     : https://prove2.me/theorems/4eebd3ee-05c4-5b77-92b2-cd2bad3076ba
-- title:
--   Erdos266: quad dom
-- statement:
--   Linear functions are eventually dominated by `k²`.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L125-L129
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L125-L129

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.quad_dom (c₀ c₁ : ℕ) : ∀ k, c₀ + c₁ + 2 ≤ k → c₁ * k + c₀ ≤ k * k := by sorry

-- Prove2me | Theorems.Thm_Erdos266_f_pos
-- name    : Erdos266.f_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:43:13.63973+00:00
-- url     : https://prove2.me/theorems/25dfbdaa-03b7-4391-984c-6a9282b48c8c
-- title:
--   Erdos266: f pos
-- statement:
--   The Erdos266 construction uses the f pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L263-L269
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L263-L269

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.f_pos {i : ℕ} {x : ℝ} (hx : (2 * i : ℝ) ≤ x) (hx0 : 0 < x) : 0 < f i x := by sorry

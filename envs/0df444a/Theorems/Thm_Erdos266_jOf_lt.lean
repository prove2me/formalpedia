-- Prove2me | Theorems.Thm_Erdos266_jOf_lt
-- name    : Erdos266.jOf_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:57:41.611834+00:00
-- url     : https://prove2.me/theorems/b338fbfb-f6c0-4e8e-8c9e-5f7fd4c96b8e
-- title:
--   Erdos266: j Of lt
-- statement:
--   The Erdos266 construction uses the j Of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L173-L177
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L173-L177

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.jOf_lt (n : ℕ) : n - cnt (kOf n) < dOf (kOf n) := by sorry

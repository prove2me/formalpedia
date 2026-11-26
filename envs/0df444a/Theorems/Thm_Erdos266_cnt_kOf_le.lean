-- Prove2me | Theorems.Thm_Erdos266_cnt_kOf_le
-- name    : Erdos266.cnt_kOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:58:12.947595+00:00
-- url     : https://prove2.me/theorems/4303cc32-03b2-4b12-9e05-3cb0f7e9ce20
-- title:
--   Erdos266: cnt k Of le
-- statement:
--   The Erdos266 construction uses the cnt k Of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L165-L171
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L165-L171

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.cnt_kOf_le (n : ℕ) : cnt (kOf n) ≤ n := by sorry

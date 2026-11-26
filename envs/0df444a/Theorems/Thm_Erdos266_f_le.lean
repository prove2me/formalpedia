-- Prove2me | Theorems.Thm_Erdos266_f_le
-- name    : Erdos266.f_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:42:54.901547+00:00
-- url     : https://prove2.me/theorems/29b9c904-9f19-589d-8025-4d6133c85186
-- title:
--   Erdos266: f le
-- statement:
--   The Erdos266 construction uses the f le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L271-L282
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L271-L282

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.f_le {i : ℕ} {x : ℝ} (hx : (2 * i : ℝ) ≤ x) (hx0 : 0 < x) :
    f i x ≤ (2 / x) ^ i := by sorry

-- Prove2me | Theorems.Thm_Erdos266_sixteen_le_bigN
-- name    : Erdos266.sixteen_le_bigN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:40:28.20957+00:00
-- url     : https://prove2.me/theorems/97637b43-7963-4e04-a959-0126a43a9133
-- title:
--   Erdos266: sixteen le big N
-- statement:
--   The Erdos266 construction uses the sixteen le big N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L89-L92
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L89-L92

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.sixteen_le_bigN {k : ℕ} (hk : 2 ≤ k) : 16 ≤ bigN k := by sorry

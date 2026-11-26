-- Prove2me | Theorems.Thm_Erdos266_tailAnchor_succ
-- name    : Erdos266.tailAnchor_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:49:33.520666+00:00
-- url     : https://prove2.me/theorems/c9192daf-5a27-4c4e-9ec3-ba724184d816
-- title:
--   Erdos266: tail Anchor succ
-- statement:
--   The Erdos266 construction uses the tail Anchor succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L291-L299
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L291-L299

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.tailAnchor_succ {i : ℕ} (hi : 1 ≤ i) (k : ℕ) :
    tailAnchor i k = blockAnchor i k + tailAnchor i (k + 1) := by sorry

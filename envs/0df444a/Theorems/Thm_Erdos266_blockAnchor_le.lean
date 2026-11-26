-- Prove2me | Theorems.Thm_Erdos266_blockAnchor_le
-- name    : Erdos266.blockAnchor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:49:04.502325+00:00
-- url     : https://prove2.me/theorems/2c856abf-61e0-4512-80ef-4f450955c7e3
-- title:
--   Erdos266: block Anchor le
-- statement:
--   The Erdos266 construction uses the block Anchor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L213-L236
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L213-L236

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.blockAnchor_le {i l : ℕ} (h2i : (2 * i : ℝ) ≤ (bigN l : ℝ)) (hi : 1 ≤ i)
    (hN2 : (2 : ℝ) ≤ (bigN l : ℝ)) :
    blockAnchor i l ≤ (l : ℝ) * (2 / (bigN l : ℝ)) := by sorry

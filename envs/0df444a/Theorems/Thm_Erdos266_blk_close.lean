-- Prove2me | Theorems.Thm_Erdos266_blk_close
-- name    : Erdos266.blk_close
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:56:15.684382+00:00
-- url     : https://prove2.me/theorems/1751d78a-d217-59a6-9a90-1820b7a07fb1
-- title:
--   Erdos266: blk close
-- statement:
--   The Erdos266 construction uses the blk close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L129-L136
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L129-L136

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.blk_close {k : ℕ} {st : AlgSt} (h : Inv k st) :
    ∀ i : Fin (dOf k),
      |Xvec k st i - ∑ j : Fin (dOf k),
          f (i.val + 1) ((((j.val + 1) * bigN k : ℕ) : ℝ) + (blk k st h j : ℝ))|
        ≤ DL (dOf k) * (1 / (bigN k : ℝ) ^ (i.val + 2)
            + (bigM k : ℝ) ^ 2 / (bigN k : ℝ) ^ (i.val + 3)) := by sorry

-- Prove2me | Theorems.Thm_Erdos266_newQ_close
-- name    : Erdos266.newQ_close
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:56:42.817309+00:00
-- url     : https://prove2.me/theorems/57e2376d-dea1-4341-835e-9dc1eef3927c
-- title:
--   Erdos266: new Q close
-- statement:
--   The Erdos266 construction uses the new Q close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L149-L155
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L149-L155

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.newQ_close {k : ℕ} {st : AlgSt} (h : Inv k st) :
    |finSum (dOf k) (k + 1) (newS k st h) + tailAnchor (dOf k + 1) (k + 1)
        - (newQ k st h : ℝ)|
      < εA (dOf (k + 1)) * bigM (k + 1) / (bigN (k + 1) : ℝ) ^ (dOf k + 2) := by sorry

-- Prove2me | Theorems.Thm_Erdos266_stepSt_eq
-- name    : Erdos266.stepSt_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:56:09.874839+00:00
-- url     : https://prove2.me/theorems/bd9c3a6f-b1b1-45be-a4a2-b36cf3391610
-- title:
--   Erdos266: step St eq
-- statement:
--   The Erdos266 construction uses the step St eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L167-L172
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L167-L172

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.stepSt_eq {k : ℕ} {st : AlgSt} (h : Inv k st) :
    stepSt k st = (newS k st h,
      if dOf (k + 1) = dOf k + 1
        then Function.update st.2 (dOf k) (newQ k st h)
        else st.2) := by sorry

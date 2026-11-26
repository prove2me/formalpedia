-- Prove2me | Theorems.Thm_Erdos266_newS_eq_of_lt
-- name    : Erdos266.newS_eq_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:55:36.389227+00:00
-- url     : https://prove2.me/theorems/4f70161c-7248-56eb-a083-62bf762d1de8
-- title:
--   Erdos266: new S eq of lt
-- statement:
--   The Erdos266 construction uses the new S eq of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L204-L206
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L204-L206

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.newS_eq_of_lt {k : ℕ} {st : AlgSt} (h : Inv k st) {l : ℕ} (hl : l ≠ k) (j : ℕ) :
    newS k st h l j = st.1 l j := by sorry

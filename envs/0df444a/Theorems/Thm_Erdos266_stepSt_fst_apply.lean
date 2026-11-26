-- Prove2me | Theorems.Thm_Erdos266_stepSt_fst_apply
-- name    : Erdos266.stepSt_fst_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:59:48.727666+00:00
-- url     : https://prove2.me/theorems/71160872-3eb9-56c3-a59f-d7577740a48d
-- title:
--   Erdos266: step St fst apply
-- statement:
--   The Erdos266 construction uses the step St fst apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L43-L46
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L43-L46

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.stepSt_fst_apply {k : ℕ} {st : AlgSt} (h : Inv k st) {l : ℕ} (hl : l ≠ k) (j : ℕ) :
    (stepSt k st).1 l j = st.1 l j := by sorry

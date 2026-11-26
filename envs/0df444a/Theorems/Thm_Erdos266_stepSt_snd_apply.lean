-- Prove2me | Theorems.Thm_Erdos266_stepSt_snd_apply
-- name    : Erdos266.stepSt_snd_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:01:00.606299+00:00
-- url     : https://prove2.me/theorems/c4724f76-54ff-47df-b900-730d9453316e
-- title:
--   Erdos266: step St snd apply
-- statement:
--   The Erdos266 construction uses the step St snd apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L48-L55
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L48-L55

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.stepSt_snd_apply {k : ℕ} {st : AlgSt} (h : Inv k st) {i : ℕ} (hi : i < dOf k) :
    (stepSt k st).2 i = st.2 i := by sorry

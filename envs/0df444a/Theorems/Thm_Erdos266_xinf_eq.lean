-- Prove2me | Theorems.Thm_Erdos266_xinf_eq
-- name    : Erdos266.xinf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:00:32.688825+00:00
-- url     : https://prove2.me/theorems/6d022e1f-ed60-5b32-8ad1-d371d4cbe990
-- title:
--   Erdos266: xinf eq
-- statement:
--   The Erdos266 construction uses the xinf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L94-L97
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L94-L97

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.xinf_eq {k i : ℕ} (hk : mseq (i + 1) ≤ k) : (run k).2 i = xinf i := by sorry

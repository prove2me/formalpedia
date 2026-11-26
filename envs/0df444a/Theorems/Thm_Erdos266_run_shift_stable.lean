-- Prove2me | Theorems.Thm_Erdos266_run_shift_stable
-- name    : Erdos266.run_shift_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:00:01.411216+00:00
-- url     : https://prove2.me/theorems/9dc80984-ea2e-521c-b0c9-7e9ddca7890c
-- title:
--   Erdos266: run shift stable
-- statement:
--   The Erdos266 construction uses the run shift stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L57-L63
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L57-L63

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.run_shift_stable {k k' : ℕ} (h2 : 2 ≤ k) (hkk : k ≤ k') {l : ℕ} (hl : l < k) (j : ℕ) :
    (run k').1 l j = (run k).1 l j := by sorry

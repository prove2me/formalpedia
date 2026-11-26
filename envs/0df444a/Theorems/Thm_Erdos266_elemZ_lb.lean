-- Prove2me | Theorems.Thm_Erdos266_elemZ_lb
-- name    : Erdos266.elemZ_lb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:58:31.62581+00:00
-- url     : https://prove2.me/theorems/3f677ffc-76d7-496f-bcb5-a0d79af5d78f
-- title:
--   Erdos266: elem Z lb
-- statement:
--   The Erdos266 construction uses the elem Z lb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L205-L210
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L205-L210

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.elemZ_lb {l j : ℕ} (hj : j < dOf l) : (bigN l : ℤ) - bigM l ≤ elemZ l j := by sorry

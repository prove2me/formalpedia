-- Prove2me | Theorems.Thm_Erdos266_Sinf_bound
-- name    : Erdos266.Sinf_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:57:32.580462+00:00
-- url     : https://prove2.me/theorems/5521eea4-3844-5ad8-87d5-8af7f26aac4d
-- title:
--   Erdos266: Sinf bound
-- statement:
--   The Erdos266 construction uses the Sinf bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L127-L129
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L127-L129

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.Sinf_bound {l j : ℕ} (hj : j < dOf l) : |Sinf l j| ≤ (bigM l : ℤ) := by sorry

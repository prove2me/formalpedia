-- Prove2me | Theorems.Thm_Erdos266_elemZ_ub
-- name    : Erdos266.elemZ_ub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:01:47.805149+00:00
-- url     : https://prove2.me/theorems/bfe93dea-9fa3-4014-affe-530dd08a4a4f
-- title:
--   Erdos266: elem Z ub
-- statement:
--   The Erdos266 construction uses the elem Z ub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L212-L220
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L212-L220

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.elemZ_ub {l j : ℕ} (hj : j < dOf l) : elemZ l j ≤ (l * bigN l : ℤ) + bigM l := by sorry

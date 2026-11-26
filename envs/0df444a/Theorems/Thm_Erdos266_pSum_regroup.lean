-- Prove2me | Theorems.Thm_Erdos266_pSum_regroup
-- name    : Erdos266.pSum_regroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:02:32.134432+00:00
-- url     : https://prove2.me/theorems/c5aaaf86-5b36-5c44-b285-e7c9b4f995c6
-- title:
--   Erdos266: p Sum regroup
-- statement:
--   The Erdos266 construction uses the p Sum regroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L437-L438
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L437-L438

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.pSum_regroup (i' k : ℕ) : pSum i' (cnt k) = finSum i' k Sinf := by sorry

-- Prove2me | Theorems.Thm_Erdos266_hasSum_aSeq
-- name    : Erdos266.hasSum_aSeq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:03:44.7508+00:00
-- url     : https://prove2.me/theorems/daf945b1-3eae-485c-872d-782dedebdbef
-- title:
--   Erdos266: has Sum a Seq
-- statement:
--   **The constructed series has the chosen rational sums.**
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L510-L537
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L510-L537

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.hasSum_aSeq (i' : ℕ) :
    HasSum (fun n => f (i' + 1) ((aSeq n : ℕ) : ℝ)) ((xinf i' : ℚ) : ℝ) := by sorry

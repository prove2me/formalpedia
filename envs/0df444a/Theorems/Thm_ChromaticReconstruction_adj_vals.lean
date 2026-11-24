-- Prove2me | Theorems.Thm_ChromaticReconstruction_adj_vals
-- name    : ChromaticReconstruction.adj_vals
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T15:02:30.048293+00:00
-- url     : https://prove2.me/theorems/81c3cd2e-9831-45e8-a044-d68f843a6b69
-- title:
--   Chromatic Reconstruction: adj vals
-- statement:
--   The values of the endpoints of an edge of `PL n p`.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L63-L66
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/PathLeafSwap.lean#L63-L66

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}

theorem ChromaticReconstruction.adj_vals {p a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) (h : s(vx n a, vx n b) ∈ (PL n p).edgeSet) :
    a + 1 = b ∨ b + 1 = a ∨ a = n ∨ b = n := by sorry

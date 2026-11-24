-- Prove2me | Theorems.Thm_ChromaticReconstruction_sum_degree_weight
-- name    : ChromaticReconstruction.sum_degree_weight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T14:27:51.178136+00:00
-- url     : https://prove2.me/theorems/b3e2c661-7bed-4c52-90f0-caab17a5ab9c
-- title:
--   Chromatic Reconstruction: sum degree weight
-- statement:
--   Degrees summed over a weight class.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L67-L84
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L67-L84

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K)
variable (w : K → ℕ)

theorem ChromaticReconstruction.sum_degree_weight (a : ℕ) :
    ∑ x ∈ univ.filter (fun x => w x = a), S.degree x =
      ((edgeTypes S w).map fun z => Multiset.count a (pairMS z)).sum := by sorry

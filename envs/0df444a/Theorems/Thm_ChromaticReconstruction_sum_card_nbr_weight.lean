-- Prove2me | Theorems.Thm_ChromaticReconstruction_sum_card_nbr_weight
-- name    : ChromaticReconstruction.sum_card_nbr_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:42:27.357504+00:00
-- url     : https://prove2.me/theorems/cbe08bae-cef3-4f1b-ae71-181f100c93fd
-- title:
--   Chromatic Reconstruction: sum card nbr weight
-- statement:
--   Edges between two distinct weight classes.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L87-L105
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L87-L105

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K)
variable (w : K → ℕ)

theorem ChromaticReconstruction.sum_card_nbr_weight {a b : ℕ} (hab : a ≠ b) :
    ∑ x ∈ univ.filter (fun x => w x = a), #{y ∈ S.neighborFinset x | w y = b} =
      Multiset.count s(a, b) (edgeTypes S w) := by sorry

-- Prove2me | Theorems.Thm_ChromaticReconstruction_sum_card_nbr_filter
-- name    : ChromaticReconstruction.sum_card_nbr_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:40:45.532316+00:00
-- url     : https://prove2.me/theorems/47004ed0-2d52-456b-8ed3-111a6fa77453
-- title:
--   Chromatic Reconstruction: sum card nbr filter
-- statement:
--   Double counting of ordered adjacent pairs.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L27-L62
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L27-L62

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K)

theorem ChromaticReconstruction.sum_card_nbr_filter (Q : K → K → Prop) [DecidableRel Q] :
    ∑ x, #{y ∈ S.neighborFinset x | Q x y} = ∑ e ∈ S.edgeFinset, pairCount Q e := by sorry

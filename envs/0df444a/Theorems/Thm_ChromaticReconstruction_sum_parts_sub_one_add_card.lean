-- Prove2me | Theorems.Thm_ChromaticReconstruction_sum_parts_sub_one_add_card
-- name    : ChromaticReconstruction.sum_parts_sub_one_add_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T13:10:15.972598+00:00
-- url     : https://prove2.me/theorems/93c37de2-e20f-4457-bfe7-9b3bcc8d5783
-- title:
--   Chromatic Reconstruction: sum parts sub one add card
-- statement:
--   `∑ (a - 1) + ℓ = k` for the parts of a partition of `k`.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CountingUpper.lean#L47-L54
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CountingUpper.lean#L47-L54

import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_CountingUpper
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.sum_parts_sub_one_add_card {k : ℕ} (μ : Nat.Partition k) :
    (μ.parts.map fun a => a - 1).sum + Multiset.card μ.parts = k := by sorry

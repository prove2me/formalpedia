-- Prove2me | Theorems.Thm_ChromaticReconstruction_bigParts_facts
-- name    : ChromaticReconstruction.bigParts_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T13:11:24.275807+00:00
-- url     : https://prove2.me/theorems/0ebf6389-5ec4-464b-810a-1b1859adf8f7
-- title:
--   Chromatic Reconstruction: big Parts facts
-- statement:
--   The Chromatic Reconstruction construction uses the big Parts facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CountingUpper.lean#L59-L80
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/CountingUpper.lean#L59-L80

import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_CountingUpper
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.bigParts_facts {k t : ℕ} {μ : Nat.Partition k} (hμ : k - t ≤ Multiset.card μ.parts) :
    Multiset.card (bigParts μ) ≤ t ∧ ∀ a ∈ bigParts μ, a ≤ t + 1 := by sorry

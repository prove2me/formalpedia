-- Prove2me | Theorems.Thm_ChromaticReconstruction_exists_ne_of_count_ne_one
-- name    : ChromaticReconstruction.exists_ne_of_count_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T14:32:32.454828+00:00
-- url     : https://prove2.me/theorems/0596cce4-f8d0-4311-b0f6-72610d360860
-- title:
--   Chromatic Reconstruction: exists ne of count ne one
-- statement:
--   The Chromatic Reconstruction construction uses the exists ne of count ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L134-L146
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L134-L146

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K]

theorem ChromaticReconstruction.exists_ne_of_count_ne_one {w : K → ℕ} {x : K} (h : Multiset.count (w x) (wts w) ≠ 1) :
    ∃ y, y ≠ x ∧ w y = w x := by sorry

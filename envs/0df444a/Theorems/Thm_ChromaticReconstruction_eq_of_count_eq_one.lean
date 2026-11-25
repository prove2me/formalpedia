-- Prove2me | Theorems.Thm_ChromaticReconstruction_eq_of_count_eq_one
-- name    : ChromaticReconstruction.eq_of_count_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:45:19.299848+00:00
-- url     : https://prove2.me/theorems/fcd57e47-5a84-4bbb-8757-00c2b448eb61
-- title:
--   Chromatic Reconstruction: eq of count eq one
-- statement:
--   The Chromatic Reconstruction construction uses the eq of count eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L125-L132
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L125-L132

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K]

theorem ChromaticReconstruction.eq_of_count_eq_one {w : K → ℕ} {a : ℕ} (h : Multiset.count a (wts w) = 1) {x y : K}
    (hx : w x = a) (hy : w y = a) : x = y := by sorry

-- Prove2me | Theorems.Thm_ChromaticReconstruction_neighborFinset_eq_of_degree_one
-- name    : ChromaticReconstruction.neighborFinset_eq_of_degree_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:28:33.237386+00:00
-- url     : https://prove2.me/theorems/59eacafa-42f9-4141-9a5d-62dcfbe95afa
-- title:
--   Chromatic Reconstruction: neighbor Finset eq of degree one
-- statement:
--   The Chromatic Reconstruction construction uses the neighbor Finset eq of degree one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L168-L174
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/WeightedIso.lean#L168-L174

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso
set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] {S : SimpleGraph K}

theorem ChromaticReconstruction.neighborFinset_eq_of_degree_one {x y : K} (hx : S.degree x = 1) (hxy : S.Adj x y) :
    S.neighborFinset x = {y} := by sorry

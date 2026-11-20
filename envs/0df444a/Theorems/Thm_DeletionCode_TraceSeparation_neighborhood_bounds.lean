-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_neighborhood_bounds
-- name    : DeletionCode.TraceSeparation.neighborhood_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:36:46.881798+00:00
-- url     : https://prove2.me/theorems/6925d50e-f604-4b7b-a338-b0ef46fb79c3
-- title:
--   Trace Separation: neighborhood bounds
-- statement:
--   A neighborhood has length 2L and stays within the corresponding finite word.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L117-L122
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L117-L122

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.neighborhood_bounds {L position n : ℕ} (hL : 1 ≤ L)
    (hmargins : 4 * L ≤ position ∧ position + 4 * L ≤ n) :
    neighborhoodLeft L position + 2 * L = neighborhoodRight L position ∧
      neighborhoodRight L position ≤ n := by sorry

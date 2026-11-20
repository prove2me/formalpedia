-- Prove2me | Theorems.Thm_DeletionCode_TraceSeparation_neighborhood_ordered
-- name    : DeletionCode.TraceSeparation.neighborhood_ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:36:37.182922+00:00
-- url     : https://prove2.me/theorems/c882dfe3-2203-4706-9ebc-54974168b74a
-- title:
--   Trace Separation: neighborhood ordered
-- statement:
--   A gap of 4L puts the entire earlier neighborhood before the later one.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L132-L135
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TraceSeparation.lean#L132-L135

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_TraceSeparation
set_option autoImplicit true
open DeletionCode DeletionCode.TraceSeparation
open AlignmentTrace FiniteConflictGraph

theorem DeletionCode.TraceSeparation.neighborhood_ordered {L a b : ℕ} (hL : 1 ≤ L)
    (hgap : a + 4 * L ≤ b) : neighborhoodRight L a ≤ neighborhoodLeft L b := by sorry

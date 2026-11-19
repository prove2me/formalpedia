-- Prove2me | Theorems.Thm_DeletionCode_CircleUniform_measurePreserving_toCircle
-- name    : DeletionCode.CircleUniform.measurePreserving_toCircle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:37:10.283955+00:00
-- url     : https://prove2.me/theorems/a1b669e6-3a5c-4e2b-86a4-f0a09f120723
-- title:
--   Circle Uniform: measure Preserving to Circle
-- statement:
--   Finite independent real weights reduce to product circle Haar measure.
--   The empty coordinate family is included.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleUniform.lean#L87-L90
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleUniform.lean#L87-L90

import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_DeletionCode_CircleUniform
set_option autoImplicit true
open DeletionCode DeletionCode.CircleUniform
open MeasureTheory Set
open scoped ENNReal

theorem DeletionCode.CircleUniform.measurePreserving_toCircle (I : Type*) [Fintype I] :
    MeasurePreserving (@toCircle I) (realWeights I) volume := by sorry

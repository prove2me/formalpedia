-- Prove2me | Theorems.Thm_DeletionCode_CircleUniform_smallArc_eq_ball
-- name    : DeletionCode.CircleUniform.smallArc_eq_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:07:26.689086+00:00
-- url     : https://prove2.me/theorems/5ac2e945-0297-489e-9acb-2ce80b2b13eb
-- title:
--   Circle Uniform: small Arc eq ball
-- statement:
--   The Circle Uniform construction uses the small Arc eq ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleUniform.lean#L23-L26
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CircleUniform.lean#L23-L26

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

theorem DeletionCode.CircleUniform.smallArc_eq_ball (Q : ℕ) :
    smallArc Q = Metric.ball (0 : UnitAddCircle) (1 / (Q : ℝ)) := by sorry

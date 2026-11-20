-- Prove2me | Theorems.Thm_Aggmetrics_DataStream_spec_joint_eq_formula
-- name    : Aggmetrics.DataStream.spec_joint_eq_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:28:58.069071+00:00
-- url     : https://prove2.me/theorems/74196e8d-ca7a-4504-a0db-693765cc3465
-- title:
--   Data Stream: spec joint eq formula
-- statement:
--   The specificity from the joint cells is the formula of the paper.
--
--   Source: https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L197-L206
-- source:
--   https://github.com/rcprati/aggmetrics-datastream-lean/blob/4175b704143eb3c39b383edf291d4075a37906fe/Aggmetrics/DataStreamProb.lean#L197-L206

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamProb
set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory
open Aggmetrics Aggmetrics.DataStream

theorem Aggmetrics.DataStream.spec_joint_eq_formula {m : ℕ} (π : Fin m → ℝ) (c : Fin m → Fin m → ℝ) (j : Fin m)
    (hπ : ∑ k, π k = 1) (hrow : ∀ k, ∑ l, c k l = 1) (hj : π j ≠ 1) :
    specJoint π c j = specFormula π c j := by sorry

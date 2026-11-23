-- Prove2me | Theorems.Thm_Deduction_LFunctionConjugation_differentiable_reg
-- name    : Deduction.LFunctionConjugation.differentiable_reg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:34:21.115302+00:00
-- url     : https://prove2.me/theorems/9ecf8bc1-3297-4ea8-879c-b685d4a87b63
-- title:
--   LFunction Conjugation: differentiable reg
-- statement:
--   The LFunction Conjugation construction uses the differentiable reg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LFunctionConj.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LFunctionConj.lean#L38-L48

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LFunctionConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
open Deduction.LFunctionConjugation
open HurwitzZeta

theorem Deduction.LFunctionConjugation.differentiable_reg (a : UnitAddCircle) : Differentiable ℂ (reg a) := by sorry

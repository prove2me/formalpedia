-- Prove2me | Theorems.Thm_DimdPolyLEAN_arcIntegral_nonneg
-- name    : DimdPolyLEAN.arcIntegral_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:27:25.691808+00:00
-- url     : https://prove2.me/theorems/c4c58297-aca9-4369-b1c5-24110e657e5d
-- title:
--   Dimd Poly LEAN: arc Integral nonneg
-- statement:
--   The Dimd Poly LEAN construction uses the arc Integral nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L482-L488
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L482-L488

module
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_RotationalAveraging
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace

theorem DimdPolyLEAN.arcIntegral_nonneg
    (I : CircleArc) {f : Circle -> ℝ}
    (hf : ∀ x ∈ arcSet I, 0 <= f x) :
    0 <= arcIntegral I f := by sorry

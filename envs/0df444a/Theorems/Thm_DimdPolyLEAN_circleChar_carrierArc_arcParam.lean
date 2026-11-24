-- Prove2me | Theorems.Thm_DimdPolyLEAN_circleChar_carrierArc_arcParam
-- name    : DimdPolyLEAN.circleChar_carrierArc_arcParam
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:27:51.215801+00:00
-- url     : https://prove2.me/theorems/a603915d-df9b-49be-862e-2aadec052c02
-- title:
--   Dimd Poly LEAN: circle Char carrier Arc arc Param
-- statement:
--   The Dimd Poly LEAN construction uses the circle Char carrier Arc arc Param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L739-L763
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L739-L763

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

theorem DimdPolyLEAN.circleChar_carrierArc_arcParam {N : Nat} (k : Fin N) (t : ℝ) :
    circleChar N (arcParam (carrierArc N k) t) =
      Complex.exp (Complex.I * (2 * Real.pi * t)) := by sorry

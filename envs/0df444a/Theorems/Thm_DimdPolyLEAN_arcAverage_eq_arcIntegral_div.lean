-- Prove2me | Theorems.Thm_DimdPolyLEAN_arcAverage_eq_arcIntegral_div
-- name    : DimdPolyLEAN.arcAverage_eq_arcIntegral_div
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:27:29.094166+00:00
-- url     : https://prove2.me/theorems/b0a03dc1-0cac-4b70-9836-0a407313fdd8
-- title:
--   Dimd Poly LEAN: arc Average eq arc Integral div
-- statement:
--   The Dimd Poly LEAN construction uses the arc Average eq arc Integral div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L490-L494
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L490-L494

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

theorem DimdPolyLEAN.arcAverage_eq_arcIntegral_div
    (I : CircleArc) (f : Circle -> ℂ) :
    arcAverage I f =
      (arcLength I)⁻¹ •
        ∫ x in arcSet I, f x ∂ μCircle := by sorry

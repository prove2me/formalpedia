-- Prove2me | Theorems.Thm_DimdPolyLEAN_circleIntegral_split_compl
-- name    : DimdPolyLEAN.circleIntegral_split_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:27:56.62502+00:00
-- url     : https://prove2.me/theorems/b647d55f-1973-46d7-9a8e-80a0aaaf56c8
-- title:
--   Dimd Poly LEAN: circle Integral split compl
-- statement:
--   The Dimd Poly LEAN construction uses the circle Integral split compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L777-L782
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L777-L782

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

theorem DimdPolyLEAN.circleIntegral_split_compl
    (s : Set Circle) (hs : MeasurableSet s) {f : Circle -> ℝ}
    (hf : MeasureTheory.Integrable f μCircle) :
    ∫ x, f x ∂ μCircle =
      ∫ x in s, f x ∂ μCircle + ∫ x in sᶜ, f x ∂ μCircle := by sorry

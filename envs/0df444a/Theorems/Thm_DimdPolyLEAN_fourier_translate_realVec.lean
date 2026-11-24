-- Prove2me | Theorems.Thm_DimdPolyLEAN_fourier_translate_realVec
-- name    : DimdPolyLEAN.fourier_translate_realVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:10:52.282064+00:00
-- url     : https://prove2.me/theorems/ddf294a7-d2e6-4c59-bc2f-67bc42046682
-- title:
--   Dimd Poly LEAN: fourier translate real Vec
-- statement:
--   The Dimd Poly LEAN construction uses the fourier translate real Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L1329-L1347
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L1329-L1347

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

theorem DimdPolyLEAN.fourier_translate_realVec {d : Nat} (a : RealVec d) (f : RealVec d -> ℂ)
    (_hf : Integrable f (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) :
    FourierTransform.fourier (fun t : RealVec d => f (t - a)) =
      fun ω : RealVec d => modulationPhase a ω * FourierTransform.fourier f ω := by sorry

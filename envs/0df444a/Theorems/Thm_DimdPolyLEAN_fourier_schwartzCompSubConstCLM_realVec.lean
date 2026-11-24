-- Prove2me | Theorems.Thm_DimdPolyLEAN_fourier_schwartzCompSubConstCLM_realVec
-- name    : DimdPolyLEAN.fourier_schwartzCompSubConstCLM_realVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:10:52.995854+00:00
-- url     : https://prove2.me/theorems/9067e438-a0f4-4527-8da5-43c2a842a1f6
-- title:
--   Dimd Poly LEAN: fourier schwartz Comp Sub Const CLM real Vec
-- statement:
--   The Dimd Poly LEAN construction uses the fourier schwartz Comp Sub Const CLM real Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L1370-L1377
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L1370-L1377

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

theorem DimdPolyLEAN.fourier_schwartzCompSubConstCLM_realVec {d : Nat}
    (f : SchwartzMap (RealVec d) ℂ) (a : RealVec d) :
    FourierTransform.fourier (schwartzCompSubConstCLM a f : RealVec d -> ℂ) =
      fun ω : RealVec d =>
        modulationPhase a ω * FourierTransform.fourier (f : RealVec d -> ℂ) ω := by sorry

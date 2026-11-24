-- Prove2me | Theorems.Thm_DimdPolyLEAN_continuous_spectrogramRep
-- name    : DimdPolyLEAN.continuous_spectrogramRep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:29:05.336035+00:00
-- url     : https://prove2.me/theorems/f4e7294e-0e3a-4a90-b71b-2ecdfb6a5cf7
-- title:
--   Dimd Poly LEAN: continuous spectrogram Rep
-- statement:
--   The Dimd Poly LEAN construction uses the continuous spectrogram Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L3209-L3213
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L3209-L3213

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

theorem DimdPolyLEAN.continuous_spectrogramRep
    {d : Nat} (h f : L2Real d) :
    Continuous fun ξ : PhaseSpace d => ((‖stftRep h f ξ‖ ^ 2 : ℝ) : ℂ) := by sorry

-- Prove2me | Theorems.Thm_DimdPolyLEAN_spectrogramRep_eq_stft_mul_star
-- name    : DimdPolyLEAN.spectrogramRep_eq_stft_mul_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:09.651786+00:00
-- url     : https://prove2.me/theorems/1aab6401-aec6-4989-a17e-4e64563355a1
-- title:
--   Dimd Poly LEAN: spectrogram Rep eq stft mul star
-- statement:
--   The Dimd Poly LEAN construction uses the spectrogram Rep eq stft mul star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L3215-L3220
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L3215-L3220

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

theorem DimdPolyLEAN.spectrogramRep_eq_stft_mul_star
    {d : Nat} (h f : L2Real d) (ξ : PhaseSpace d) :
    ((‖stftRep h f ξ‖ ^ 2 : ℝ) : ℂ) =
      stftRep h f ξ * star (stftRep h f ξ) := by sorry

-- Prove2me | Theorems.Thm_DimdPolyLEAN_stftRep_congr_left
-- name    : DimdPolyLEAN.stftRep_congr_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:28:23.957801+00:00
-- url     : https://prove2.me/theorems/1551fab8-fd06-41ae-868f-b121e29372aa
-- title:
--   Dimd Poly LEAN: stft Rep congr left
-- statement:
--   The Dimd Poly LEAN construction uses the stft Rep congr left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L2060-L2064
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L2060-L2064

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

theorem DimdPolyLEAN.stftRep_congr_left
    {d : Nat} {h h' f : L2Real d} (hh : h = h') :
    stftRep h f = stftRep h' f := by sorry

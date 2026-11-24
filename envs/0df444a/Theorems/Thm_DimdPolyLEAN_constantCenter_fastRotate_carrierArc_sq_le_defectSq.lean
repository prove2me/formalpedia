-- Prove2me | Theorems.Thm_DimdPolyLEAN_constantCenter_fastRotate_carrierArc_sq_le_defectSq
-- name    : DimdPolyLEAN.constantCenter_fastRotate_carrierArc_sq_le_defectSq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:10:33.871996+00:00
-- url     : https://prove2.me/theorems/2f8cb835-7ca1-43c6-9573-32a84f304d8c
-- title:
--   Dimd Poly LEAN: constant Center fast Rotate carrier Arc sq le defect Sq
-- statement:
--   The Dimd Poly LEAN construction uses the constant Center fast Rotate carrier Arc sq le defect Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L784-L821
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L784-L821

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

theorem DimdPolyLEAN.constantCenter_fastRotate_carrierArc_sq_le_defectSq
    {N : Nat} (k : Fin N) {c u : ℂ} (hc : c ≠ 0) :
    arcLength (carrierArc N k) * ‖u‖ ^ 2 <=
      Crot *
        arcIntegral (carrierArc N k)
          (fun x => (‖c + circleChar N x * u‖ - ‖c‖) ^ 2) := by sorry

-- Prove2me | Theorems.Thm_DimdPolyLEAN_period_smul_muCircle_mk_image_carrierArc_Ioc
-- name    : DimdPolyLEAN.period_smul_muCircle_mk_image_carrierArc_Ioc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:10:18.569805+00:00
-- url     : https://prove2.me/theorems/b24930fe-1bf3-4f29-8b47-3131174dbee8
-- title:
--   Dimd Poly LEAN: period smul mu Circle mk image carrier Arc Ioc
-- statement:
--   The Dimd Poly LEAN construction uses the period smul mu Circle mk image carrier Arc Ioc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L361-L375
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L361-L375

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

theorem DimdPolyLEAN.period_smul_muCircle_mk_image_carrierArc_Ioc {N : Nat} (k : Fin N) :
    ENNReal.ofReal (2 * Real.pi) *
        μCircle
          ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
            Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) =
      ENNReal.ofReal (arcLength (carrierArc N k)) := by sorry

alias «DimdPolyLEAN».«period_smul_μCircle_mk_image_carrierArc_Ioc» := DimdPolyLEAN.period_smul_muCircle_mk_image_carrierArc_Ioc

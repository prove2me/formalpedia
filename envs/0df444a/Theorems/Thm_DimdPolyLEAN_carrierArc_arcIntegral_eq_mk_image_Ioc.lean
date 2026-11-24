-- Prove2me | Theorems.Thm_DimdPolyLEAN_carrierArc_arcIntegral_eq_mk_image_Ioc
-- name    : DimdPolyLEAN.carrierArc_arcIntegral_eq_mk_image_Ioc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:10:22.368837+00:00
-- url     : https://prove2.me/theorems/e2034e4a-d12a-4d55-9333-36684559bf68
-- title:
--   Dimd Poly LEAN: carrier Arc arc Integral eq mk image Ioc
-- statement:
--   The Dimd Poly LEAN construction uses the carrier Arc arc Integral eq mk image Ioc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L388-L395
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L388-L395

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

theorem DimdPolyLEAN.carrierArc_arcIntegral_eq_mk_image_Ioc
    {N : Nat} (k : Fin N) (f : Circle -> ℝ) :
    arcIntegral (carrierArc N k) f =
      ∫ x in QuotientAddGroup.mk ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        f x ∂ μCircle := by sorry

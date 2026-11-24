-- Prove2me | Theorems.Thm_DimdPolyLEAN_carrierArc_arcSet_ae_eq_mk_image_Ioc
-- name    : DimdPolyLEAN.carrierArc_arcSet_ae_eq_mk_image_Ioc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:01:46.317802+00:00
-- url     : https://prove2.me/theorems/dfc6f7af-dff1-4161-ac26-5e52f16b11d4
-- title:
--   Dimd Poly LEAN: carrier Arc arc Set ae eq mk image Ioc
-- statement:
--   The Dimd Poly LEAN construction uses the carrier Arc arc Set ae eq mk image Ioc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L295-L299
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L295-L299

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

theorem DimdPolyLEAN.carrierArc_arcSet_ae_eq_mk_image_Ioc {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =ᵐ[μCircle]
      QuotientAddGroup.mk ''
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by sorry

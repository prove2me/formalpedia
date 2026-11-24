-- Prove2me | Theorems.Thm_DimdPolyLEAN_carrierArc_arcSet_eq_mk_image_Ioc_union_left
-- name    : DimdPolyLEAN.carrierArc_arcSet_eq_mk_image_Ioc_union_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:05:30.962801+00:00
-- url     : https://prove2.me/theorems/77040746-a7ae-4940-8cf3-8d8d1e69c8fc
-- title:
--   Dimd Poly LEAN: carrier Arc arc Set eq mk image Ioc union left
-- statement:
--   The Dimd Poly LEAN construction uses the carrier Arc arc Set eq mk image Ioc union left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L191-L212
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L191-L212

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

theorem DimdPolyLEAN.carrierArc_arcSet_eq_mk_image_Ioc_union_left {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =
      (QuotientAddGroup.mk ''
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) ∪
        {(QuotientAddGroup.mk ((carrierArc N k).left) : Circle)} := by sorry

-- Prove2me | Theorems.Thm_DimdPolyLEAN_circleIntegral_union_finset
-- name    : DimdPolyLEAN.circleIntegral_union_finset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:27:56.373051+00:00
-- url     : https://prove2.me/theorems/8043802b-9de0-44f6-a1d4-361d85f04d1b
-- title:
--   Dimd Poly LEAN: circle Integral union finset
-- statement:
--   The Dimd Poly LEAN construction uses the circle Integral union finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L765-L775
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L765-L775

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

theorem DimdPolyLEAN.circleIntegral_union_finset
    {ι : Type} [Fintype ι] (I : ι -> CircleArc)
    (hdisj : Pairwise fun i j => Disjoint (arcSet (I i)) (arcSet (I j)))
    {f : Circle -> ℝ}
    (hf : ∀ i, MeasureTheory.IntegrableOn f (arcSet (I i)) μCircle) :
    ∫ x in (⋃ i, arcSet (I i)), f x ∂ μCircle =
      ∑ i, arcIntegral (I i) f := by sorry

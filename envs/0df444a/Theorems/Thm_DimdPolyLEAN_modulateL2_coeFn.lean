-- Prove2me | Theorems.Thm_DimdPolyLEAN_modulateL2_coeFn
-- name    : DimdPolyLEAN.modulateL2_coeFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:01:22.606664+00:00
-- url     : https://prove2.me/theorems/71af5aab-80fd-4de2-9fc6-e86ea6ae06bf
-- title:
--   Dimd Poly LEAN: modulate L2 coe Fn
-- statement:
--   The Dimd Poly LEAN construction uses the modulate L2 coe Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L1882-L1885
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L1882-L1885

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

theorem DimdPolyLEAN.modulateL2_coeFn {d : Nat} (ω : RealVec d) (f : L2Real d) :
    ((modulateL2 ω f : L2Real d) : RealVec d -> ℂ)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
        fun t => modulationPhase ω t * (f : RealVec d -> ℂ) t := by sorry

-- Prove2me | Theorems.Thm_DimdPolyLEAN_continuous_modulateL2
-- name    : DimdPolyLEAN.continuous_modulateL2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:20.083698+00:00
-- url     : https://prove2.me/theorems/249eb959-2820-476b-8e87-07e1aa026ffb
-- title:
--   Dimd Poly LEAN: continuous modulate L2
-- statement:
--   The Dimd Poly LEAN construction uses the continuous modulate L2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L2122-L2134
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L2122-L2134

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

theorem DimdPolyLEAN.continuous_modulateL2 {d : Nat} {X : Type*} [TopologicalSpace X]
    {ω : X -> RealVec d} {h : X -> L2Real d}
    (hω : Continuous ω) (hh : Continuous h) :
    Continuous fun x : X => modulateL2 (ω x) (h x) := by sorry

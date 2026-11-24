-- Prove2me | Theorems.Thm_DimdPolyLEAN_symplecticFourierRep_eq_vectorFourier
-- name    : DimdPolyLEAN.symplecticFourierRep_eq_vectorFourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:28:02.412801+00:00
-- url     : https://prove2.me/theorems/63485057-f67f-484a-9adb-d37eadc9a7f3
-- title:
--   Dimd Poly LEAN: symplectic Fourier Rep eq vector Fourier
-- statement:
--   The Dimd Poly LEAN construction uses the symplectic Fourier Rep eq vector Fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L952-L961
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L952-L961

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

theorem DimdPolyLEAN.symplecticFourierRep_eq_vectorFourier {d : Nat}
    (F : PhaseSpace d -> ℂ) (ξ : PhaseSpace d) :
    symplecticFourierRep F ξ =
      VectorFourier.fourierIntegral Real.fourierChar volume
        (symplecticFormLinear (d := d)) F ξ := by sorry

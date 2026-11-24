-- Prove2me | Theorems.Thm_DimdPolyLEAN_ambiguityRep_eq_integral_of_ae_eq
-- name    : DimdPolyLEAN.ambiguityRep_eq_integral_of_ae_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:06:03.030819+00:00
-- url     : https://prove2.me/theorems/5d73327c-2c01-4a5f-917d-f794213f82bf
-- title:
--   Dimd Poly LEAN: ambiguity Rep eq integral of ae eq
-- statement:
--   The ambiguity integral can use almost-everywhere equal representatives.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L1596-L1614
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L1596-L1614

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

theorem DimdPolyLEAN.ambiguityRep_eq_integral_of_ae_eq
    {d : ℕ} {f g : L2Real d} {F G : RealVec d → ℂ}
    (hf : (f : RealVec d → ℂ) =ᵐ[volume] F)
    (hg : (g : RealVec d → ℂ) =ᵐ[volume] G) (ξ : PhaseSpace d) :
    ambiguityRep f g ξ = ∫ t : RealVec d,
      F (t + (1 / 2 : ℝ) • ξ.1) * star (G (t - (1 / 2 : ℝ) • ξ.1)) *
        modulationPhase ξ.2 t := by sorry

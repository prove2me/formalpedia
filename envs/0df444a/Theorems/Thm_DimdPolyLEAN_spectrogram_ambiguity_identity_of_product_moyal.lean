-- Prove2me | Theorems.Thm_DimdPolyLEAN_spectrogram_ambiguity_identity_of_product_moyal
-- name    : DimdPolyLEAN.spectrogram_ambiguity_identity_of_product_moyal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:29:12.855598+00:00
-- url     : https://prove2.me/theorems/244ebd67-cb0e-4023-849a-646d3009c138
-- title:
--   Dimd Poly LEAN: spectrogram ambiguity identity of product moyal
-- statement:
--   The Dimd Poly LEAN construction uses the spectrogram ambiguity identity of product moyal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L3222-L3236
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/ImportedAnalyticInputs.lean#L3222-L3236

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

theorem DimdPolyLEAN.spectrogram_ambiguity_identity_of_product_moyal
    {d : Nat}
    (hmoyal : ∀ (h f : L2Real d) (ξ : PhaseSpace d),
      symplecticFourierRep
          (fun η : PhaseSpace d => stftRep h f η * star (stftRep h f η)) ξ =
        ambiguityRep f f ξ * star (ambiguityRep h h ξ))
    (h f : L2Real d) (ξ : PhaseSpace d) :
    symplecticFourierRep
        (fun η : PhaseSpace d => ((‖stftRep h f η‖ ^ 2 : ℝ) : ℂ)) ξ =
      ambiguityRep f f ξ * star (ambiguityRep h h ξ) := by sorry

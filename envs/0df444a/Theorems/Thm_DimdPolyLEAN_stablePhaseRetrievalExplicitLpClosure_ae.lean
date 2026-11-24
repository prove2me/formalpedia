-- Prove2me | Theorems.Thm_DimdPolyLEAN_stablePhaseRetrievalExplicitLpClosure_ae
-- name    : DimdPolyLEAN.stablePhaseRetrievalExplicitLpClosure_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:26:53.329403+00:00
-- url     : https://prove2.me/theorems/f8bf8067-17f9-405b-9ab1-71e3d8b56f06
-- title:
--   Dimd Poly LEAN: stable Phase Retrieval Explicit Lp Closure ae
-- statement:
--   The Dimd Poly LEAN construction uses the stable Phase Retrieval Explicit Lp Closure ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Auxiliary.lean#L848-L863
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Auxiliary.lean#L848-L863

module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Auxiliary
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN

theorem DimdPolyLEAN.stablePhaseRetrievalExplicitLpClosure_ae
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (P : (Fin d -> ℂ) -> ℂ) (hP : P ∈ Set.range (explicitEvalPkappa κ)) :
    ∃ C_P : ℝ, 0 < C_P ∧
      ∀ Q : MeasureTheory.Lp ℂ 2 (explicitGamma d),
        Q ∈ closure
          { f : MeasureTheory.Lp ℂ 2 (explicitGamma d) |
            ∃ P ∈ Set.range (explicitEvalPkappa κ), f =ᵐ[explicitGamma d] P } →
          ∃ θ : ℂ, ‖θ‖ = 1 ∧
            explicitGaussianL2DistanceSq P (fun z => θ * Q z) ≤
              C_P ^ 2 * explicitModulusDistanceSq P (Q : (Fin d -> ℂ) -> ℂ) := by sorry

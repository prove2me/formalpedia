-- Prove2me | Theorems.Thm_DimdPolyLEAN_stablePhaseRetrievalExplicitRange
-- name    : DimdPolyLEAN.stablePhaseRetrievalExplicitRange
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:26:38.90003+00:00
-- url     : https://prove2.me/theorems/0fa264ed-38a9-427b-9dad-b93c65d2c191
-- title:
--   Dimd Poly LEAN: stable Phase Retrieval Explicit Range
-- statement:
--   The Dimd Poly LEAN construction uses the stable Phase Retrieval Explicit Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Auxiliary.lean#L285-L297
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Auxiliary.lean#L285-L297

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

theorem DimdPolyLEAN.stablePhaseRetrievalExplicitRange
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (P : (Fin d -> ℂ) -> ℂ) (hP : P ∈ Set.range (explicitEvalPkappa κ)) :
    ∃ C_P : ℝ, 0 < C_P ∧
      ∀ Q : (Fin d -> ℂ) -> ℂ, Q ∈ Set.range (explicitEvalPkappa κ) →
        ∃ θ : ℂ, ‖θ‖ = 1 ∧
          ∫ z, ‖P z - θ * Q z‖ ^ 2 ∂ explicitGamma d
            ≤ C_P ^ 2 *
              ∫ z, (‖P z‖ - ‖Q z‖) ^ 2 ∂ explicitGamma d := by sorry

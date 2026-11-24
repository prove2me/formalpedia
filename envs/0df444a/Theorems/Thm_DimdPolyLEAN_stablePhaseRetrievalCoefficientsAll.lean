-- Prove2me | Theorems.Thm_DimdPolyLEAN_stablePhaseRetrievalCoefficientsAll
-- name    : DimdPolyLEAN.stablePhaseRetrievalCoefficientsAll
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:26:36.867563+00:00
-- url     : https://prove2.me/theorems/cb2085cb-bb5e-4de3-b664-81c1ca556f0b
-- title:
--   Dimd Poly LEAN: stable Phase Retrieval Coefficients All
-- statement:
--   The Dimd Poly LEAN construction uses the stable Phase Retrieval Coefficients All property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Auxiliary.lean#L266-L283
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Auxiliary.lean#L266-L283

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

theorem DimdPolyLEAN.stablePhaseRetrievalCoefficientsAll
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (F : Finsupp (Fin d -> ℕ) ℂ) :
    ∃ C_F : ℝ, 0 < C_F ∧
      ∀ Q : Finsupp (Fin d -> ℕ) ℂ,
        ∃ θ : ℂ, ‖θ‖ = 1 ∧
          ∫ z, ‖explicitEvalPkappa κ F z - θ * explicitEvalPkappa κ Q z‖ ^ 2
              ∂ explicitGamma d
            ≤ C_F ^ 2 *
              ∫ z, (‖explicitEvalPkappa κ F z‖ - ‖explicitEvalPkappa κ Q z‖) ^ 2
                ∂ explicitGamma d := by sorry

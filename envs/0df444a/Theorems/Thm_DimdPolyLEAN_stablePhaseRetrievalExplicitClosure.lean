-- Prove2me | Theorems.Thm_DimdPolyLEAN_stablePhaseRetrievalExplicitClosure
-- name    : DimdPolyLEAN.stablePhaseRetrievalExplicitClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:27:06.999281+00:00
-- url     : https://prove2.me/theorems/901762fd-00da-4bbe-b971-9cbdf5daca44
-- title:
--   Dimd Poly LEAN: stable Phase Retrieval Explicit Closure
-- statement:
--   The Dimd Poly LEAN construction uses the stable Phase Retrieval Explicit Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Auxiliary.lean#L770-L788
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Auxiliary.lean#L770-L788

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

theorem DimdPolyLEAN.stablePhaseRetrievalExplicitClosure
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ)
    (P : (Fin d -> ℂ) -> ℂ) (hP : P ∈ Set.range (explicitEvalPkappa κ)) :
    ∃ C_P : ℝ, 0 < C_P ∧
      ∀ Q : (Fin d -> ℂ) -> ℂ, Q ∈ explicitClosureOfHermitePolys κ →
        explicitPhaseOptimizedDistanceSq P Q ≤
          C_P ^ 2 * explicitModulusDistanceSq P Q := by sorry

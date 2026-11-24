-- Prove2me | Theorems.Thm_DimdPolyLEAN_explicitHermitePolys_subset_explicitClosure
-- name    : DimdPolyLEAN.explicitHermitePolys_subset_explicitClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:45:27.343412+00:00
-- url     : https://prove2.me/theorems/1e24247d-55e0-41a2-b43e-348a93cffe6d
-- title:
--   Dimd Poly LEAN: explicit Hermite Polys subset explicit Closure
-- statement:
--   The Dimd Poly LEAN construction uses the explicit Hermite Polys subset explicit Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Auxiliary.lean#L503-L511
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Auxiliary.lean#L503-L511

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

theorem DimdPolyLEAN.explicitHermitePolys_subset_explicitClosure
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ) :
    Set.range (explicitEvalPkappa κ) ⊆ explicitClosureOfHermitePolys κ := by sorry

-- Prove2me | Theorems.Thm_Auto_aux_eLpNorm_orbit_comp
-- name    : Auto.aux_eLpNorm_orbit_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:47:29.543528+00:00
-- url     : https://prove2.me/theorems/803ddebc-6bc6-4362-9e73-c8f9cf3167d3
-- title:
--   Auto: aux e Lp Norm orbit comp
-- statement:
--   `Lᵖ` norms are invariant under joint forward orbits.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1164-L1170
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1164-L1170

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section

theorem Auto.aux_eLpNorm_orbit_comp {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {n : ℕ} (S : ErgodicSystem X μ n) (k : Fin n → ℕ)
    {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    (F : X → E) (p : ℝ≥0∞) (hF : AEStronglyMeasurable F μ) :
    eLpNorm (F ∘ aux_orbit S.transformation k) p μ = eLpNorm F p μ := by sorry

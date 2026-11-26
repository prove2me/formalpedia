-- Prove2me | Theorems.Thm_Auto_aux_overlap_index_eq
-- name    : Auto.aux_overlap_index_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:36:56.164014+00:00
-- url     : https://prove2.me/theorems/3e39630f-6224-5de4-88f4-e459d5bca712
-- title:
--   Auto: aux overlap index eq
-- statement:
--   Different coordinate overlap intervals cannot meet at distinct integer
--   indices when their total width is less than one.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L557-L576
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L557-L576

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

theorem Auto.aux_overlap_index_eq {n : ℕ} {ε δ : ℝ}
    (hwidth : ε + δ < 1) (u : aux_RVector n)
    (hu : ∀ i, 0 ≤ u i ∧ u i < ε) (i j : Fin n) (s : ℝ)
    (m₁ m₂ : ℤ)
    (h₁ : ε - u i ≤ s - (m₁ : ℝ) ∧
      s - (m₁ : ℝ) < ε + δ - u i)
    (h₂ : ε - u j ≤ s - (m₂ : ℝ) ∧
      s - (m₂ : ℝ) < ε + δ - u j) :
    m₁ = m₂ := by sorry

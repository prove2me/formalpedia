-- Prove2me | Theorems.Thm_Auto_aux_cuboidEmbed_product_eq_zero_of_no_common_overlap
-- name    : Auto.aux_cuboidEmbed_product_eq_zero_of_no_common_overlap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:39:22.561799+00:00
-- url     : https://prove2.me/theorems/5d13568e-b3d3-4922-9fc6-84c10ff74595
-- title:
--   Auto: aux cuboid Embed product eq zero of no common overlap
-- statement:
--   Outside the common overlap intervals, one cuboid factor vanishes and so
--   does their product.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L582-L612
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L582-L612

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

theorem Auto.aux_cuboidEmbed_product_eq_zero_of_no_common_overlap
    {n : ℕ} (hn : 0 < n) {ε δ : ℝ} (hε : ε < 1)
    (hwidth : ε + δ < 1) (a : Fin n → aux_ZVector n → ℝ)
    (k : aux_ZVector n) (u : aux_RVector n) (s : ℝ)
    (hu : ∀ j, 0 ≤ u j ∧ u j < ε)
    (hno : ¬ ∃ m : ℤ, ∀ i, ε - u i ≤ s - (m : ℝ) ∧
      s - (m : ℝ) < ε + δ - u i) :
    (∏ i, aux_cuboidEmbed ε δ i (a i)
      (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s)) = 0 := by sorry

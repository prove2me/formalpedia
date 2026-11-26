-- Prove2me | Theorems.Thm_Auto_aux_cuboidEmbed_translateAxis_exists_or_eq_zero
-- name    : Auto.aux_cuboidEmbed_translateAxis_exists_or_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:39:14.297284+00:00
-- url     : https://prove2.me/theorems/e1281ec9-50c6-5845-ae70-1a3b9bf78788
-- title:
--   Auto: aux cuboid Embed translate Axis exists or eq zero
-- statement:
--   At a base point in the small cube, a cuboid lift is either its one
--   discrete translate on an overlap interval, or it vanishes.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L515-L551
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L515-L551

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

theorem Auto.aux_cuboidEmbed_translateAxis_exists_or_eq_zero {n : ℕ}
    {ε δ : ℝ} (hε : ε < 1) (hεδ : ε + δ < 1) (i : Fin n)
    (a : aux_ZVector n → ℝ) (k : aux_ZVector n) (u : aux_RVector n)
    (s : ℝ) (hu : ∀ j, 0 ≤ u j ∧ u j < ε) :
    (∃ m : ℤ, ε - u i ≤ s - (m : ℝ) ∧
        s - (m : ℝ) < ε + δ - u i ∧
        aux_cuboidEmbed ε δ i a
          (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s) =
          a (aux_translateAxisInt k i m)) ∨
      (¬ ∃ m : ℤ, ε - u i ≤ s - (m : ℝ) ∧
          s - (m : ℝ) < ε + δ - u i) ∧
        aux_cuboidEmbed ε δ i a
          (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s) = 0 := by sorry

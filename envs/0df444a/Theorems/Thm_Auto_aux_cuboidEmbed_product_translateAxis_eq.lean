-- Prove2me | Theorems.Thm_Auto_aux_cuboidEmbed_product_translateAxis_eq
-- name    : Auto.aux_cuboidEmbed_product_translateAxis_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:39:13.90206+00:00
-- url     : https://prove2.me/theorems/f80c72f6-9bda-4ccb-9112-c1b56c5a687c
-- title:
--   Auto: aux cuboid Embed product translate Axis eq
-- statement:
--   If one parameter lies in every overlap interval, the product of cuboid
--   lifts is exactly the corresponding diagonal discrete product.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L498-L509
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L498-L509

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

theorem Auto.aux_cuboidEmbed_product_translateAxis_eq {n : ℕ} {ε δ : ℝ}
    (hε : ε < 1) (hεδ : ε + δ < 1)
    (a : Fin n → aux_ZVector n → ℝ) (k : aux_ZVector n)
    (u : aux_RVector n) (m : ℤ) (s : ℝ)
    (hu : ∀ j, 0 ≤ u j ∧ u j < ε)
    (hs : ∀ i, ε - u i ≤ s - m ∧ s - m < ε + δ - u i) :
    (∏ i, aux_cuboidEmbed ε δ i (a i)
        (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s)) =
      ∏ i, a i (aux_translateAxisInt k i m) := by sorry

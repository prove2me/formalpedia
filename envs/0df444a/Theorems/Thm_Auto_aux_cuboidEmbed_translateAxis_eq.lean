-- Prove2me | Theorems.Thm_Auto_aux_cuboidEmbed_translateAxis_eq
-- name    : Auto.aux_cuboidEmbed_translateAxis_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:36:47.257372+00:00
-- url     : https://prove2.me/theorems/0e9d11cf-bd94-5fee-8ebc-22298a0d26cc
-- title:
--   Auto: aux cuboid Embed translate Axis eq
-- statement:
--   On a common overlap interval, the `i`th cuboid lift recovers the
--   corresponding discrete translate.  This is the exact pointwise
--   continuous-to-discrete identity.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L443-L492
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L443-L492

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

theorem Auto.aux_cuboidEmbed_translateAxis_eq {n : ℕ} {ε δ : ℝ}
    (hε : ε < 1) (hεδ : ε + δ < 1) (i : Fin n)
    (a : aux_ZVector n → ℝ) (k : aux_ZVector n) (u : aux_RVector n)
    (m : ℤ) (s : ℝ) (hu : ∀ j, 0 ≤ u j ∧ u j < ε)
    (hs : ε - u i ≤ s - m ∧ s - m < ε + δ - u i) :
    aux_cuboidEmbed ε δ i a
        (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s) =
      a (aux_translateAxisInt k i m) := by sorry

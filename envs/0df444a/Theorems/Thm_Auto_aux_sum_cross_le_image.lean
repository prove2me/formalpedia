-- Prove2me | Theorems.Thm_Auto_aux_sum_cross_le_image
-- name    : Auto.aux_sum_cross_le_image
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:39:21.14573+00:00
-- url     : https://prove2.me/theorems/d5629b3c-434f-5fae-908b-dc6070bf9cc6
-- title:
--   Auto: aux sum cross le image
-- statement:
--   Sum terms supported on dyadic crossings using their distinct source labels.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L305-L325
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L305-L325

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_sum_cross_le_image {J : ℕ} {b : Fin (J + 1) → ℤ}
    (hb : Monotone b) (q : Fin J → ℝ≥0∞) (V : ℤ → ℝ≥0∞)
    (hsupport : ∀ j, j ∉ aux_crossIndices b → q j = 0)
    (hle : ∀ j ∈ aux_crossIndices b, q j ≤ V (b j.castSucc)) :
    ∑ j, q j ≤ ∑ k ∈ (aux_crossIndices b).image (fun j ↦ b j.castSucc), V k := by sorry

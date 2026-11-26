-- Prove2me | Theorems.Thm_Auto_aux_sum_cross_le_kappa
-- name    : Auto.aux_sum_cross_le_kappa
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:31.290742+00:00
-- url     : https://prove2.me/theorems/3abd565f-c67f-48a6-966b-7622e7d046ef
-- title:
--   Auto: aux sum cross le kappa
-- statement:
--   Extend the crossing estimate to the full finite set of occupied labels.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L328-L336
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L328-L336

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_sum_cross_le_kappa {J : ℕ} {b : Fin (J + 1) → ℤ}
    (hb : Monotone b) (q : Fin J → ℝ≥0∞) (V : ℤ → ℝ≥0∞)
    (hsupport : ∀ j, j ∉ aux_crossIndices b → q j = 0)
    (hle : ∀ j ∈ aux_crossIndices b, q j ≤ V (b j.castSucc))
    (κ : Finset ℤ)
    (hκ : (aux_crossIndices b).image (fun j ↦ b j.castSucc) ⊆ κ) :
    ∑ j, q j ≤ ∑ k ∈ κ, V k := by sorry

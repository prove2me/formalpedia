-- Prove2me | Theorems.Thm_Auto_aux_dyadicLocal_sum_le_variation_rpow
-- name    : Auto.aux_dyadicLocal_sum_le_variation_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:53.412046+00:00
-- url     : https://prove2.me/theorems/54d6e750-6f3e-5bb2-b01c-4761256a757e
-- title:
--   Auto: aux dyadic Local sum le variation rpow
-- statement:
--   The local variation of a clamped chain is bounded by its dyadic variation.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L126-L139
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L126-L139

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_dyadicLocal_sum_le_variation_rpow {B : Type*} [SeminormedAddCommGroup B]
    {J : ℕ} {k : ℤ} {t : Fin (J + 1) → ℝ} (ht : Monotone t)
    (a : ℝ → B) (r : ℝ) (hr : 1 ≤ r) :
    (∑ j : Fin J,
      (‖a (aux_dyadicLocalChain J k t j.succ) -
        a (aux_dyadicLocalChain J k t j.castSucc)‖₊ : ℝ≥0∞) ^ r) ≤
      (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r := by sorry

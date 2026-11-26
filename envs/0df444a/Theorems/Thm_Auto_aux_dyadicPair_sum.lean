-- Prove2me | Theorems.Thm_Auto_aux_dyadicPair_sum
-- name    : Auto.aux_dyadicPair_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:59.224465+00:00
-- url     : https://prove2.me/theorems/210d4d33-419f-49b6-81cd-b43130fb3e37
-- title:
--   Auto: aux dyadic Pair sum
-- statement:
--   The energy of the padded dyadic pair has one nonzero increment.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L179-L190
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L179-L190

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_dyadicPair_sum {B : Type*} [SeminormedAddCommGroup B]
    {M : ℕ} {k : ℤ} (a : ℝ → B) (r : ℝ) (hr : 0 < r)
    (x : aux_dyadicInterval k) :
    (∑ j : Fin (M + 1),
      (‖a (aux_dyadicPairChain (M + 1) k x j.succ) -
        a (aux_dyadicPairChain (M + 1) k x j.castSucc)‖₊ : ℝ≥0∞) ^ r) =
      (‖a x - a ((2 : ℝ) ^ k)‖₊ : ℝ≥0∞) ^ r := by sorry

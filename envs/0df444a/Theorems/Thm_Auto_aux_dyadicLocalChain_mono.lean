-- Prove2me | Theorems.Thm_Auto_aux_dyadicLocalChain_mono
-- name    : Auto.aux_dyadicLocalChain_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:38:27.911082+00:00
-- url     : https://prove2.me/theorems/a045e711-dc49-4bd3-a8e5-1eb775bdc7f4
-- title:
--   Auto: aux dyadic Local Chain mono
-- statement:
--   Clamping preserves monotonicity.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L106-L108
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L106-L108

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.aux_dyadicLocalChain_mono {J : ℕ} {k : ℤ} {t : Fin (J + 1) → ℝ}
    (ht : Monotone t) : Monotone (aux_dyadicLocalChain J k t) := by sorry

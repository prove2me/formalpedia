-- Prove2me | Theorems.Thm_Auto_aux_setIntegral_sum_overlapContribution
-- name    : Auto.aux_setIntegral_sum_overlapContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:40:29.520004+00:00
-- url     : https://prove2.me/theorems/58f01ead-52d4-4c74-b206-debb338c3daf
-- title:
--   Auto: aux set Integral sum overlap Contribution
-- statement:
--   Restricting the finite overlap expansion to its scale interval does not
--   change its integral.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L906-L935
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L906-L935

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

theorem Auto.aux_setIntegral_sum_overlapContribution {n : ℕ}
    (hn : 0 < n) {ε δ : ℝ} (hεδ : ε ≤ δ) (hwidth : ε + δ < 1)
    (a : Fin n → aux_ZVector n → ℝ) (k : aux_ZVector n)
    (u : aux_RVector n) (N : ℕ) (hu : ∀ i, 0 ≤ u i ∧ u i < ε) :
    ∫ s in Ico (0 : ℝ) N, ∑ q : Fin N,
        aux_overlapContribution ε δ a k u q.val s =
      aux_overlapWidth hn ε δ u * ∑ q : Fin N,
        ∏ i, a i (aux_translateAxisInt k i (q.val : ℤ)) := by sorry

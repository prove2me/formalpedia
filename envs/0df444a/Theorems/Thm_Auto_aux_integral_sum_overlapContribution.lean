-- Prove2me | Theorems.Thm_Auto_aux_integral_sum_overlapContribution
-- name    : Auto.aux_integral_sum_overlapContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:40:50.491937+00:00
-- url     : https://prove2.me/theorems/c41955d6-946e-416b-b5eb-a7aab2f8ba46
-- title:
--   Auto: aux integral sum overlap Contribution
-- statement:
--   The full scale integral of the finite overlap expansion factors as the
--   common overlap width times the discrete diagonal sum.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L861-L900
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L861-L900

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

theorem Auto.aux_integral_sum_overlapContribution {n : ℕ} (hn : 0 < n)
    {ε δ : ℝ} (hεδ : ε ≤ δ) (a : Fin n → aux_ZVector n → ℝ)
    (k : aux_ZVector n) (u : aux_RVector n) (N : ℕ)
    (hu : ∀ i, 0 ≤ u i ∧ u i < ε) :
    ∫ s : ℝ, ∑ q : Fin N, aux_overlapContribution ε δ a k u q.val s =
      aux_overlapWidth hn ε δ u * ∑ q : Fin N,
        ∏ i, a i (aux_translateAxisInt k i (q.val : ℤ)) := by sorry

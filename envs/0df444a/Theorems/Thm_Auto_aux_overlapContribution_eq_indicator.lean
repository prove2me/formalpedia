-- Prove2me | Theorems.Thm_Auto_aux_overlapContribution_eq_indicator
-- name    : Auto.aux_overlapContribution_eq_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:37:10.026985+00:00
-- url     : https://prove2.me/theorems/8004f213-339c-4e1c-8bef-e0f7e4c2afdb
-- title:
--   Auto: aux overlap Contribution eq indicator
-- statement:
--   An overlap contribution is the indicator of its common half-open
--   interval times its diagonal lattice coefficient.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L832-L848
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L832-L848

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

theorem Auto.aux_overlapContribution_eq_indicator {n : ℕ} (hn : 0 < n)
    (ε δ : ℝ) (a : Fin n → aux_ZVector n → ℝ) (k : aux_ZVector n)
    (u : aux_RVector n) (q : ℕ) (s : ℝ) :
    aux_overlapContribution ε δ a k u q s =
      (Ico (aux_overlapLower hn ε u q) (aux_overlapUpper hn ε δ u q)).indicator
        (fun _ ↦ ∏ i, a i (aux_translateAxisInt k i (q : ℤ))) s := by sorry

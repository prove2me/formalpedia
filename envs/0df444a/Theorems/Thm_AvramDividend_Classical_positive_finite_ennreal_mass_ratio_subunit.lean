-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_finite_ennreal_mass_ratio_subunit
-- name    : AvramDividend.Classical.positive_finite_ennreal_mass_ratio_subunit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T19:41:34.513997+00:00
-- url     : https://prove2.me/theorems/f7017ed8-4161-4d06-a932-bc72d88f8360
-- title:
--   Strict positive subdrift renewal measure mass gives a real contraction ratio
-- statement:
--   For a strictly positive discounted Esscher renewal-kernel mass m strictly smaller than the positive BV drift δ, prove the exact real ratio (m.toReal)/δ lies in (0,1), retaining the ENNReal-to-real coercions. This supplies the ρ contraction parameter of corrected BV renewal kernel series data (9be5ada9), the BV C1 branch and cstar_lt_top.
-- source:
--   Pinned Mathlib ENNReal.toReal_pos, ENNReal.toReal_lt_toReal, ENNReal.toReal_ofReal; BV root discounted tail kernel mass package.

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic

open scoped ENNReal

theorem AvramDividend.Classical.positive_finite_ennreal_mass_ratio_subunit
    (m : ℝ≥0∞) (δ : ℝ)
    (hδ : 0 < δ) (hmpos : 0 < m)
    (hmbound : m < ENNReal.ofReal δ) :
    0 < m.toReal / δ ∧ m.toReal / δ < 1 := by sorry

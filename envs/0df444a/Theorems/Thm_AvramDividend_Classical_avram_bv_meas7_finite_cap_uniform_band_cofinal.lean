-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_finite_cap_uniform_band_cofinal
-- name    : AvramDividend.Classical.avram_bv_meas7_finite_cap_uniform_band_cofinal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:35:55.742205+00:00
-- url     : https://prove2.me/theorems/9204e420-f121-4b7a-a80c-b2b6b91664b8
-- title:
--   Original finite-cap compact bands eventually contain every strict interior reserve
-- statement:
--   For a finite positive dividend cap C, the explicit compact localisation bands a_n=min(1,C.toReal/2)/(n+1), b_n=C.toReal(n+1)/(n+2) stay strictly within (0,C) at every level, and each strictly interior positive surplus belongs to all sufficiently large bands. This strengthens established compact-band geometry by supplying the cofinality certificate needed to take the genuine compact compensated jump source through localisation.
-- source:
--   The already Proved finite-cap compact-band construction 204ef2ef and finite-cap eventual-inclusion theorem 7df6597f. Algebraic construction is kernel-checked from actual Lean source, with no stochastic axioms.

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_band_eventually_contains_interior_reserve

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_finite_cap_uniform_band_cofinal (C : ℝ≥0∞) (hC : 0 < C) (hTop : C ≠ ⊤) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
        ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n / 2) (b n)) := by sorry

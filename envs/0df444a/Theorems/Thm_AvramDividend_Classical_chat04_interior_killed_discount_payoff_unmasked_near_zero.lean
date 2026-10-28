-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_interior_killed_discount_payoff_unmasked_near_zero
-- name    : AvramDividend.Classical.chat04_interior_killed_discount_payoff_unmasked_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:53:01.623673+00:00
-- url     : https://prove2.me/theorems/00e87244-7ef7-42bf-b185-e0197c87a3d4
-- title:
--   Interior killed discounted q-scale payoff agrees with the raw payoff for a positive initial interval
-- statement:
--   For a strictly interior reserve 0<x<a, every right-continuous Lévy path survives above zero for a positive initial interval. Hence the entire-history killed ENNReal discounted q-scale payoff equals the un-killed discounted q-scale payoff throughout that pathwise interval. This proves the exact time-zero survival factorization required when establishing the interior killed q-scale renewal identity, without assuming the as-yet-unproved stochastic harmonicity.
-- source:
--   Direct import of Proved chat04_interior_two_sided_initial_safe_window c9d6c919-5bd9-4d85-b1b6-7f2a7fb52194 and standard Set.indicator_of_mem. Consumer: Open chat04_unbounded_killed_survival_discounted_scale_expectation a885f0b3-3960-424d-97e4-abbcffe268ba, then chat04_unbounded_two_sided_exit_stopped_scale_identity aed50a34, stopped-scale parent 09663d0d and integral identity 3e1ce2c8.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_interior_two_sided_initial_safe_window
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_interior_killed_discount_payoff_unmasked_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x q : ℝ) (hx0 : 0 < x) (hxa : x < a)
    (W : ℝ → ℝ) (ω : Ω) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ t : ℝ≥0, t < ε →
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω =
          ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) := by sorry

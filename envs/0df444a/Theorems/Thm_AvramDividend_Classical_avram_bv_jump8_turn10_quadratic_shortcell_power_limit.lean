-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn10_quadratic_shortcell_power_limit
-- name    : AvramDividend.Classical.avram_bv_jump8_turn10_quadratic_shortcell_power_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:41:53.917189+00:00
-- url     : https://prove2.me/theorems/b193c1eb-44de-40fc-a2d5-1b6dcdaee650
-- title:
--   Quadratic short-cell expectation error preserves the Poisson exponential power limit
-- statement:
--   For a bounded family q_n∈[0,1] with deterministic first-order expansion 1-a/(n+1) and nonnegative O(1/(n+1)²) remainder, the powers q_n^(n+1) converge to exp(-a). Pure real analysis using the proved quadratic power Lipschitz f5f31bb9 and Real.tendsto_one_add_div_pow_exp.
-- source:
--   For a bounded family q_n∈[0,1] with deterministic first-order expansion 1-a/(n+1) and nonnegative O(1/(n+1)²) remainder, the powers q_n^(n+1) converge to exp(-a). Pure real analysis using the proved quadratic power Lipschitz f5f31bb9 and Real.tendsto_one_add_div_pow_exp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn10_quadratic_shortcell_power_limit
    (a C : ℝ) (q : ℕ → ℝ) (hC : 0 ≤ C)
    (hq : ∀ n, 0 ≤ q n ∧ q n ≤ 1)
    (hErr : ∀ n,
      0 ≤ q n - (1 - a / ((n + 1 : ℕ) : ℝ)) ∧
      q n - (1 - a / ((n + 1 : ℕ) : ℝ)) ≤
        C / ((n + 1 : ℕ) : ℝ) ^ 2) :
    Tendsto (fun n : ℕ => (q n) ^ (n + 1)) atTop
      (𝓝 (Real.exp (-a))) := by sorry

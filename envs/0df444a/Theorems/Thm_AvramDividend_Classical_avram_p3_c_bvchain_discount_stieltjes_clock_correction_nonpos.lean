-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_discount_stieltjes_clock_correction_nonpos
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_discount_stieltjes_clock_correction_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:29:10.132756+00:00
-- url     : https://prove2.me/theorems/87f6694d-796e-41ed-90f8-de59a2297581
-- title:
--   Nonpositive finite-grid and strict-terminal exponential-discount clock corrections for nonnegative candidate values
-- statement:
--   Every discount-factor increment across an increasing finite grid is nonpositive for q≥0. The sum of these increments times nonnegative candidate values and the terminal increment to b is nonpositive, including zero/repeated cells and zero terminal extension. This is the clock correction in the original P3-C strict-horizon finite-grid BV budget.
-- source:
--   Elementary monotonicity of the original exponential discount along the bounded-variation stopping mesh, Avram Proposition 4(i) Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open scoped NNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p3_c_bvchain_discount_stieltjes_clock_correction_nonpos
    (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hmono : ∀ i, i < n → u i ≤ u (i + 1))
    (b : ℝ≥0) (hfinal : u n ≤ b)
    (f : ℕ → ℝ) (fb : ℝ)
    (hf : ∀ i, i < n → 0 ≤ f (i + 1)) (hfb : 0 ≤ fb) :
    (∑ i ∈ Finset.range n,
        (Real.exp (-(q * (u (i + 1) : ℝ))) -
          Real.exp (-(q * (u i : ℝ)))) * f (i + 1)) +
      (Real.exp (-(q * (b : ℝ))) -
        Real.exp (-(q * (u n : ℝ)))) * fb ≤ 0 := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_dividend_rightlimit_discount_mesh_gap
-- name    : AvramDividend.Classical.avram_wave6_chat09_original_dividend_rightlimit_discount_mesh_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:42:50.507809+00:00
-- url     : https://prove2.me/theorems/b04aa727-748c-486b-8f39-80922a8911d5
-- title:
--   Original dividend full-right-limit discount mesh timing error is bounded by mesh width times total paid
-- statement:
--   For any actual original monotone dividend strategy path, a monotone finite time grid of mesh width at most m, and nonnegative discount q, the sum of left-minus-right exponential discount weights multiplied by post-payment cumulative dividend increments is at most q m times the full cumulative dividend right-limit increment. This is a deterministic source-faithful bound for every path, including atoms and continuous or singular-continuous Stieltjes dividends. It controls the mesh-timing error needed to pass left-clock Stieltjes inequalities to right-endpoint source-grid estimates without assuming the desired stochastic HJB inequality.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), Section 5.4: stochastic verification finite-horizon Stieltjes mesh discount passage.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_chat09_original_dividend_rightlimit_discount_mesh_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (hu : Monotone u)
    (n : ℕ) (m : ℝ) (hm : 0 ≤ m)
    (hmesh : ∀ i < n, ((u (i + 1) : ℝ) - (u i : ℝ)) ≤ m) :
    (∑ i ∈ Finset.range n,
      (Real.exp (-(q * (u i : ℝ))) -
         Real.exp (-(q * (u (i + 1) : ℝ)))) *
       (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) ≤
       q * m * (rightLimit D (u n) ω - rightLimit D (u 0) ω) := by sorry

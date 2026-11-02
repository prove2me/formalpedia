-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_zero_cap_original_any_index_discounted_right_payment_residual_tsum_zero
-- name    : AvramDividend.Classical.avram_wave6_05_zero_cap_original_any_index_discounted_right_payment_residual_tsum_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:26:23.062302+00:00
-- url     : https://prove2.me/theorems/b902fe80-9be8-4aca-aa36-987f74580acd
-- title:
--   Zero cap: entire discounted sum of all actual original right-payment cash-plus-V residuals is exactly zero
-- statement:
--   For literal ENNReal zero cap, the cap-linear extension V is affine with slope one along each permitted original right payment interval. Every individual payment residual δ_t+V(U_t−δ_t)−V(U_t) is exactly zero, including at time zero, before ruin and when the underlying Lévy path also jumps. Consequently its exponentially discounted tsum is exactly zero for any index set A of permitted times, without separately imposing countability, summability, or a sign on q. The actual set of jump times of a finite-variation control is countable, but the stronger zero-function theorem avoids making that extra assumption. Continuous and singular-continuous parts of D remain unrestricted and are accounted for separately by the complete Stieltjes measure theorem.
-- source:
--   Direct application of canonically Proved exact zero-cap original right-payment V drop at each permitted time, followed by a zero-function tsum calculation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_zero_cap_original_alltime_affine_dividend_jump_exact

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_05_zero_cap_original_any_index_discounted_right_payment_residual_tsum_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (q : ℝ) (w V : ℝ → ℝ)
    (hVzero : ∀ y : ℝ,
      V y = if y ≤ 0 then w y else w 0 + y)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (0 : ℝ≥0∞) D)
    (ω : Ω) (A : Set ℝ≥0)
    (hA : ∀ t : A, (t : ℝ≥0) = 0 ∨
      ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω) :
    (∑' t : A, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        V (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        V (riskProcess X x D (t : ℝ≥0) ω))) = 0 := by sorry

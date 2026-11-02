-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_global_discounted_dividend_measure_finite
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_global_discounted_dividend_measure_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:14:36.648728+00:00
-- url     : https://prove2.me/theorems/2dccb65c-5baf-4ff6-9b21-66270dcf51ec
-- title:
--   Automatic local finiteness of the genuine discounted dividend Stieltjes measure for capped source strategies
-- statement:
--   Under the full cap-interval gradient secant and admissibility, the original-process exponentially discounted dividendMeasure integral over every finite monotone pre-ruin time horizon is finite, even when the controlled reserve equals zero or the cap and when the dividend measure has singular-continuous, diffuse and atomic components, including the initial time-zero atom. No localisation to strict interior and no a priori finiteness of dividend reward is assumed.
-- source:
--   Proved closed-horizon original-source actual measure budget ed9de935-bfdb-4622-806d-2bf785db782e, finiteness of finite ENNReal sums and ne_top_of_le_ne_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_global_closed_discounted_stieltjes_grid_budget

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_global_discounted_dividend_measure_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    :
    (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≠ ⊤ := by sorry

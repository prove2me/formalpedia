-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_discounted_cell_left_weighted_signed_domination
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_discounted_cell_left_weighted_signed_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:32:10.398623+00:00
-- url     : https://prove2.me/theorems/40b56206-3120-412a-9931-f974bf3be868
-- title:
--   Original pre-ruin discounted Stieltjes cell signed domination with exact left-time value weight
-- statement:
--   For every admissible finite-cap dividend strategy and every pre-ruin cell (a,b], the full actual discounted dividend Stieltjes lower integral is dominated by exp(-q a) times the corresponding source-frozen cap-linear value drop, expressed in ENNReal. This includes singular-continuous, diffuse, countably atomic, and boundary-contact payments. No strict interior localisation is assumed.
-- source:
--   Proved generic left-endpoint discount envelope; Proved dividendMeasure_Ioc_rightLimit; Proved full-cap cap-linear extension secant, right-limit monotonicity, and admissible post-payment solvency.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_discounted_stieltjes_cell_le_left_endpoint_discount_mass
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_discounted_cell_left_weighted_signed_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) *
        ENNReal.ofReal (V (x + X.X b ω - rightLimit D a ω) -
          V (x + X.X b ω - rightLimit D b ω)) := by sorry

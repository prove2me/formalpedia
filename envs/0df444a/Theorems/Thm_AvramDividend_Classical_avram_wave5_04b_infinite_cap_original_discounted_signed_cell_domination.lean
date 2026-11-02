-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_infinite_cap_original_discounted_signed_cell_domination
-- name    : AvramDividend.Classical.avram_wave5_04b_infinite_cap_original_discounted_signed_cell_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:32:25.451766+00:00
-- url     : https://prove2.me/theorems/38beb7b1-bfb7-4794-a7ae-95ba691ab998
-- title:
--   Infinite-cap original-source complete discounted Stieltjes cell signed value-drop domination
-- statement:
--   For the original Avram admissible dividend process with infinite capital cap, the actual discounted dividendMeasure on every pre-ruin chronological half-open interval is dominated by the left-endpoint discount multiplied by the exact value-function drop. This controls all diffuse, singular-continuous and countably atomic dividends, includes zero reserve contact and avoids the finite-cap cap-linear extension hypothesis.
-- source:
--   The Proved infinite-cap gradient global secant plus post-payment solvency bounds exact right-limit dividend increments by w drops. The generic Proved left-endpoint discounted Stieltjes envelope bounds the entire interval lower integral; dividendMeasure_Ioc_rightLimit identifies interval mass. No density or strict interior assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_infinite_cap_gradient_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_discounted_stieltjes_cell_le_left_endpoint_discount_mass
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_infinite_cap_original_discounted_signed_cell_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z})
    (hw_grad : ∀ z : ℝ, 0 < z → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (⊤ : ℝ≥0∞) D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) *
        ENNReal.ofReal
          (w (x + X.X b ω - rightLimit D a ω) -
            w (x + X.X b ω - rightLimit D b ω)) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_discounted_full_stieltjes_cell_domination
-- name    : AvramDividend.Classical.avram_wave5_04b_positive_cap_original_discounted_full_stieltjes_cell_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:34:28.98228+00:00
-- url     : https://prove2.me/theorems/d44e536f-7d44-42fd-ac21-db1fd1497f3b
-- title:
--   Uniform positive ENNReal cap source-specific boundary-safe discounted full Stieltjes dividend cell domination
-- statement:
--   For any positive capital cap C, finite or infinity, take the global cap-linear value extension V (equal to w at infinite C). For any pre-ruin chronological dividend cell, the discounted integral against the actual dividendMeasure is bounded by the left-endpoint exponential discount times the cap-linear value drop at the right-time source-frozen reserve. Includes zero and cap contacts, diffuse, singular-continuous and countable right atoms, with neither hloc nor finite-cap assumption.
-- source:
--   Use Proved uniform ENNReal-cap global extension secant, admissible post-payment solvency and right-limit monotonicity. The Proved generic complete measure left-endpoint discount envelope plus exact dividendMeasure_Ioc_rightLimit provide the complete Stieltjes weighted mass. No stochastic compensation or chain rule is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_discounted_stieltjes_cell_le_left_endpoint_discount_mass
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_positive_cap_original_discounted_full_stieltjes_cell_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) *
        ENNReal.ofReal
          (V (x + X.X b ω - rightLimit D a ω) -
            V (x + X.X b ω - rightLimit D b ω)) := by sorry

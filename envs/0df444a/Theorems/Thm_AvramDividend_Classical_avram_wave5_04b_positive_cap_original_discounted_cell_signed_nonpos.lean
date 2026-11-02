-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_discounted_cell_signed_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_positive_cap_original_discounted_cell_signed_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:47:32.720173+00:00
-- url     : https://prove2.me/theorems/8b796314-e62a-4769-84d5-34c5ea2c2e14
-- title:
--   All positive ENNReal-cap original-source real signed discounted full Stieltjes dividend control without hloc
-- statement:
--   For an admissible original dividend strategy, any positive finite or infinite cap, and a pre-ruin chronological dividend cell (a,b], the real value of the actual exponentially discounted lower integral against dividendMeasure plus exp(-qa) times the source-frozen cap-linear value change is nonpositive. This is a true signed real-valued boundary-safe Stieltjes correction covering diffuse, singular-continuous and countably right-atomic payments, without an interior reserve assumption.
-- source:
--   Proved uniform positive ENNReal-cap source-specific discounted full measure domination converted to reals; the positive-cap extension global secant ensures the value drop is nonnegative; exact post-payment solvency and monotone right-limit dividends supply its ordered arguments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_discounted_full_stieltjes_cell_domination
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_positive_cap_original_discounted_cell_signed_nonpos
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
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (a : ℝ))) *
        (V (x + X.X b ω - rightLimit D b ω) -
          V (x + X.X b ω - rightLimit D a ω)) ≤ 0 := by sorry

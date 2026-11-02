-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_discounted_cell_left_weighted_signed_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_discounted_cell_left_weighted_signed_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:47:20.924224+00:00
-- url     : https://prove2.me/theorems/eb4d626b-517f-42cc-9d78-583e73a6df21
-- title:
--   Source-specific full-Stieltjes left-weighted signed dividend correction nonpositive without interior reserve localisation
-- statement:
--   For an original spectrally negative Levy process with admissible finite-cap dividend strategy, q≥0, and any pre-ruin chronological cell (a,b], the toReal of the actual discounted lower integral of dividendMeasure plus exp(-qa) times the source-frozen cap-linear value change is nonpositive. The result is boundary-safe at reserve zero and the cap and covers diffuse, singular-continuous, countably right-atomic, and time-zero-compatible payments, requiring no derivative at a boundary.
-- source:
--   Take toReal of Proved source-specific left-weighted ENNReal domination; use prior Proved cell mass signed domination and nonnegativity to establish nonnegative finite value drop; convert ENNReal products and rearrange.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_discounted_cell_left_weighted_signed_domination
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_interval_full_dividend_measure_signed_domination

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_discounted_cell_left_weighted_signed_nonpos
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
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (a : ℝ))) *
        (V (x + X.X b ω - rightLimit D b ω) -
          V (x + X.X b ω - rightLimit D a ω)) ≤ 0 := by sorry

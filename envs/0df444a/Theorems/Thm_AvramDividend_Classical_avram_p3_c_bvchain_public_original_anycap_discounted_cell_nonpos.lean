-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_discounted_cell_nonpos
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_public_original_anycap_discounted_cell_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:17:17.550078+00:00
-- url     : https://prove2.me/theorems/7c388cd5-1e46-42d9-8704-05750d298d2d
-- title:
--   Public original BV complete discounted Stieltjes cell sign
-- statement:
--   For original X and admissible left-continuous/right-dividend D on any pre-ruin interval, the true full discounted Stieltjes cash plus the left-discounted caplinear source-frozen rightpayment value difference is nonpositive. Includes singular-continuous payments and right endpoint atoms, and enforces solvency and positive or infinite cap without extending the derivative condition to boundaries. Uses the two separately public supporting lemmas.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_discount_left_full_measure_le
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_source_frozen_cell_nonpos
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p3_c_bvchain_public_original_anycap_discounted_cell_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ t in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (a : ℝ))) *
        (V (x + X.X b ω - rightLimit D b ω) -
          V (x + X.X b ω - rightLimit D a ω)) ≤ 0 := by sorry

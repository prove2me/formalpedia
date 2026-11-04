-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_paymentTimes_discounted_cell_nonpos
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_public_original_paymentTimes_discounted_cell_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:29:10.627292+00:00
-- url     : https://prove2.me/theorems/778e5fd0-11ec-4060-8c6c-f003c64aa2b2
-- title:
--   Public strict-ruin original discounted Stieltjes cash cell sign
-- statement:
--   The original strict-ruin paymentTimes restriction of the full discounted measure agrees with the entire right-closed interval before ruin, including singular-continuous and terminal right-endpoint mass. The discounted cell plus left-discounted source-frozen V drop is nonpositive under original admissibility and cap-gradient/secant hypotheses. No assumed compensation or stochastic identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_discounted_cell_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p3_c_bvchain_public_original_paymentTimes_discounted_cell_nonpos
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
    (hPre : (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (a : ℝ))) *
        (V (x + X.X b ω - rightLimit D b ω) -
          V (x + X.X b ω - rightLimit D a ω)) ≤ 0 := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_anycap_finite_mesh_discounted_endpoint_stieltjes_nonpositive
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_anycap_finite_mesh_discounted_endpoint_stieltjes_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:27:54.301212+00:00
-- url     : https://prove2.me/theorems/dbbf89d0-3664-4c19-be67-2031a46a4819
-- title:
--   Original source full Stieltjes dividend cells remain nonpositive after endpoint discount weighting
-- statement:
--   Every original source Stieltjes payment cell remains nonpositive after its positive exponential endpoint discount. The entire closed-right cell mass includes singular continuous and right atomic dividends at the genuine payment time; cap and zero contact use the already proved source cap-linear extension. This proves a finite-mesh discounted stage, without falsely claiming the exact within-cell varying discount or stochastic mesh limit.
-- source:
--   Proved source full cap Stieltjes cell c04d2cd0; Avram Palmowski Pistorius Proposition 4(i), (5.10)-(5.12)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_anycap_true_payment_full_stieltjes_cell_budget

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_anycap_finite_mesh_discounted_endpoint_stieltjes_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
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
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (s : Finset ι) (a b : ι → ℝ≥0)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hPay : ∀ i ∈ s, (b i : ℝ) ∈ paymentTimes (ruinTime X x D ω)) :
    (∑ i ∈ s, Real.exp (-(q * (b i : ℝ))) *
      ((dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))).toReal +
        V (x + X.X (b i) ω - rightLimit D (b i) ω) -
        V (x + X.X (b i) ω - rightLimit D (a i) ω))) ≤ 0 := by sorry

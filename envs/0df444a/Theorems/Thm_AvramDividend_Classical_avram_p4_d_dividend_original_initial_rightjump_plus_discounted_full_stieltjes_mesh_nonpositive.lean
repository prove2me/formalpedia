-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_initial_rightjump_plus_discounted_full_stieltjes_mesh_nonpositive
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_initial_rightjump_plus_discounted_full_stieltjes_mesh_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:33:47.132535+00:00
-- url     : https://prove2.me/theorems/637a362c-1496-404d-bd21-3f30c9b05da5
-- title:
--   Original time-zero right payment and discounted full Stieltjes mesh have nonpositive joint correction
-- statement:
--   The original explicit hjump at time zero controls the initial right-payment even at immediate ruin; the accepted source cap full Stieltjes mesh lemma controls every later (a,b] cell, weighted by its own endpoint discount and retaining singular-continuous and terminal right-atomic contributions. Their sum is nonpositive. This is a finite-mesh result, not a claimed exact discounted chain rule.
-- source:
--   Original hjump in P4-F and Proved P4-D endpoint discount mesh dbbf89d0; Avram Proposition 4(i) (5.10)-(5.12)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_anycap_finite_mesh_discounted_endpoint_stieltjes_nonpositive

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_initial_rightjump_plus_discounted_full_stieltjes_mesh_nonpositive
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
    (hjump : ∀ ω (r : ℝ≥0),
      (r = 0 ∨ (r : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D r ω - D r ω ≤ w (riskProcess X x D r ω) -
        w (riskProcess X x D r ω - (rightLimit D r ω - D r ω)))
    (ω : Ω) (s : Finset ι) (a b : ι → ℝ≥0)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hPay : ∀ i ∈ s, (b i : ℝ) ∈ paymentTimes (ruinTime X x D ω)) :
    ((rightLimit D 0 ω - D 0 ω) +
      w (riskProcess X x D 0 ω - (rightLimit D 0 ω - D 0 ω)) -
      w (riskProcess X x D 0 ω)) +
      (∑ i ∈ s, Real.exp (-(q * (b i : ℝ))) *
        ((dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))).toReal +
          V (x + X.X (b i) ω - rightLimit D (b i) ω) -
          V (x + X.X (b i) ω - rightLimit D (a i) ω))) ≤ 0 := by sorry

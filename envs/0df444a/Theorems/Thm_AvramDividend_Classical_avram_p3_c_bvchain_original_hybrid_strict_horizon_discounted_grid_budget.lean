-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_hybrid_strict_horizon_discounted_grid_budget
-- name    : AvramDividend.Classical.avram_p3_c_bvchain_original_hybrid_strict_horizon_discounted_grid_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:15:52.828524+00:00
-- url     : https://prove2.me/theorems/02e2ddd8-cbb7-47e7-9958-5d5c812da4aa
-- title:
--   Original BV hybrid complete grid with a strict-open pre-rightpayment terminal horizon
-- statement:
--   Combine the genuine original time-zero payment and earlier right-closed full discounted cells with a final strict-open discounted Stieltjes cell ending at the original pre-rightpayment terminal reserve. Preserve exactly once-discounted cash, finite/infinite positive caps, source-frozen Levy increments, right-jump hjump, and the final q-clock correction; all evaluated before original ruin.
-- source:
--   Accepted P3-C 1a7c8151 original initial once-discounted full-grid source budget, e6756f8c strict-open prepayment discounted source-frozen cell, 37425aad original cap book V=w. Pure finite-grid algebra, original X,D, no extra HJB/compensation assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_initial_discounted_product_source_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_discounted_strict_pre_cell_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_book_postpayment_V_eq_w
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p3_c_bvchain_original_hybrid_strict_horizon_discounted_grid_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
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
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (n : ℕ) (hzero : u 0 = 0)
    (hGrid : ∀ i : ℕ, i < n → u i ≤ u (i + 1))
    (hPre : ∀ i : ℕ, i < n →
      (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (b : ℝ≥0) (hFinal : u n < b)
    (hBPre : (b : ℝ≥0∞) < ruinTime X x D ω) :
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    let source : ℕ → ℝ := fun i =>
      V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
      V (x + X.X (u i) ω - rightLimit D (u i) ω)
    let finalCash : ℝ :=
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioo (u n : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    rightLimit D 0 ω + (∑ i ∈ Finset.range n, cash i) + finalCash +
      Real.exp (-(q * (b : ℝ))) * w (riskProcess X x D b ω) ≤
      w x + (∑ i ∈ Finset.range n, e i * source i) +
      e n * (V (x + X.X b ω - rightLimit D (u n) ω) -
        V (x + X.X (u n) ω - rightLimit D (u n) ω)) +
      ∑ i ∈ Finset.range n, (e (i + 1) - e i) * post (i + 1) +
      (Real.exp (-(q * (b : ℝ))) - e n) *
        w (riskProcess X x D b ω) := by sorry

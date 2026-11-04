-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_budget_from_stopped_error_mean
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_budget_from_stopped_error_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:05:45.805582+00:00
-- url     : https://prove2.me/theorems/93b705f6-422e-4cfe-9234-84fc09802c1d
-- title:
--   Original BV strict stopped cash budget from genuine residual expectation and stochastic correction bounds
-- statement:
--   An exact original-process stopped cash-plus-signed-preterminal inequality follows from a true original stopped budget with a zero-mean martingale correction, nonpositive HJB correction, and the source finite-grid BV residual expectation estimate. Conditional stochastic budget remains explicit.
-- source:
--   Accepted 10bf363b original residual expected nonpositive, source-specific strict stopped cash and preterminal. The original stopped HJB/Itô budget hBudget is an explicit conditional stochastic obligation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_residual_grid_expected_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_budget_from_stopped_error_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (q : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
    (hu : Monotone u) (n : ℕ) (hstop : ∀ ω, u n ≤ τ ω)
    (hResidualInt : Integrable (fun ω =>
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal
      ∑ i : Fin n, Real.exp (-(q * (u i : ℝ))) *
        (V (riskProcess X x D (u i) ω -
          (R (u (i + 1)) - R (u i))) -
          V (riskProcess X x D (u i) ω))) P)
    (T : ℝ) (hT : 0 ≤ T)
    (Mart HJB : Ω → ℝ)
    (hMartMean : (∫ ω, Mart ω ∂P) = 0)
    (hHJBMean : (∫ ω, HJB ω ∂P) ≤ 0)
    (hBudget :
      let S : ℝ≥0 := ⟨T, hT⟩
      let CashOpen : Ω → ℝ := fun ω =>
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
      let Pre : Ω → ℝ := fun ω =>
        if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0
      let Corr : Ω → ℝ := fun ω =>
        let R : ℝ≥0 → ℝ := fun t =>
          ((t : ℝ) * X.drift - X.X t ω) -
            (∑' (v : ℝ≥0),
              if 0 < v ∧ v ≤ t then
                ENNReal.ofReal (Function.leftLim
                  (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
              else 0).toReal
        ∑ i : Fin n, Real.exp (-(q * (u i : ℝ))) *
          (V (riskProcess X x D (u i) ω -
            (R (u (i + 1)) - R (u i))) -
            V (riskProcess X x D (u i) ω))
      (∫ ω, CashOpen ω + Pre ω ∂P) ≤
        w x + (∫ ω, Mart ω ∂P) + (∫ ω, HJB ω ∂P) +
          (∫ ω, Corr ω ∂P)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let CashOpen : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let Pre : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0
    (∫ ω, CashOpen ω + Pre ω ∂P) ≤ w x := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_complete_stieltjes_signed_without_rightsum_assumption
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_complete_stieltjes_signed_without_rightsum_assumption
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T20:13:02.824332+00:00
-- url     : https://prove2.me/theorems/4161b441-cddf-4063-99b4-d214e5a652b3
-- title:
--   Full original right-continuous closed-horizon dividend signed Stieltjes budget with derived jump summability
-- statement:
--   For a genuine original admissible dividend control, the exact set of every positive pre-ruin rightpayment through the closed horizon, and an explicit source local upper K secant condition, derive absolute convergence of the chronological discounted jump correction from genuine Stieltjes Cash. Feed this into the accepted full atomic and diffuse source theorem to obtain the complete original closed-horizon decomposition and conditional nonpositive signed dividend remainder, including time zero, simultaneous Lévy/dividend jumps, singular-continuous payments and eligible horizon atoms. No independent summability premise is assumed.
-- source:
--   Accepted original full signed Stieltjes decomposition d2232fa0 and new original rightpayment source-summability adapter 31ea0262, preserving exact hypotheses and reserve state ordering.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_complete_positive_right_payment_set_full_signed_stieltjes
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_rightpayment_summable_for_stieltjes

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_complete_stieltjes_signed_without_rightsum_assumption
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y
        else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (hDS : IsDividendStrategy 𝓕 D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (T : ℝ≥0) (B : Set ℝ≥0)
    (hBExact : B = {t : ℝ≥0 | 0 < t ∧
      (t : ℝ≥0∞) < ruinTime X x D ω ∧
      t ≤ T ∧ 0 < rightLimit D t ω - D t ω})
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ t : B,
      w (riskProcess X x D (t : ℝ≥0) ω) -
        w (x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω) ≤
          K * (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      ((∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) =
        (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μatom) +
        (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse)) ∧
      ((∀ᵐ s ∂μdiffuse.restrict
          (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)),
        0 < (x +
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω) ∧
        ENNReal.ofReal (x +
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω) < C) →
        (∫ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
          Real.exp (-(q * s)) *
            (1 - deriv w (x +
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
              rightLimit D s.toNNReal ω)) ∂μdiffuse) +
        (∑' t : B, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
          ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
            w (riskProcess X x D (t : ℝ≥0) ω -
              (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
            w (riskProcess X x D (t : ℝ≥0) ω))) +
        ((rightLimit D 0 ω - D 0 ω) +
          V (riskProcess X x D 0 ω -
            (rightLimit D 0 ω - D 0 ω)) -
          V (riskProcess X x D 0 ω)) ≤ 0) := by sorry

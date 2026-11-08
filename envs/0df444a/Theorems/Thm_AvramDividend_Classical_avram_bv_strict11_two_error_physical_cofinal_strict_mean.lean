-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict11_two_error_physical_cofinal_strict_mean
-- name    : AvramDividend.Classical.avram_bv_strict11_two_error_physical_cofinal_strict_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:37:53.612502+00:00
-- url     : https://prove2.me/theorems/5887efa9-3c35-4b2e-b09b-582e7cd97fff
-- title:
--   Original stopped BV cofinal signed mean bound from separately integrable two-scale C1 and contact errors
-- statement:
--   For the actual admissible dividend strategy and original strict stopped cash plus terminal, a centred two-index martingale, nonpositive generator contribution, and independently integrable interior and contact errors with a two-scale vanishing expected upper budget imply the full-horizon strict expected payoff bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_two_scale_centered_positive_error_diagonal
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict11_two_error_physical_cofinal_strict_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hu0 : ∀ n, 0 ≤ u n) (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n)
    (F B : ℕ → Ω → ℝ)
    (hF : ∀ n ω, F n ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0))
    (M ErrCell ErrContact : ℕ → ℕ → Ω → ℝ)
    (η : ℕ → ℝ) (hηpos : ∀ n, 0 < η n)
    (hηzero : Tendsto η atTop (nhds (0 : ℝ)))
    (hM : ∀ n k, Integrable (M n k) P ∧
      (∫ ω, M n k ω ∂P) = 0)
    (hCell : ∀ n k, Integrable (fun ω => max (ErrCell n k ω) 0) P)
    (hContact : ∀ n k, Integrable (fun ω => max (ErrContact n k ω) 0) P)
    (hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hBudget : ∀ n k, ∀ᵐ ω ∂P,
      F n ω ≤ w x + (M n k ω + B n ω) +
        max (ErrCell n k ω) 0 + max (ErrContact n k ω) 0)
    (hApprox : ∀ n (ε : ℝ), 0 < ε → ∃ k,
      (∫ ω, max (ErrCell n k ω) 0 ∂P) +
        (∫ ω, max (ErrContact n k ω) 0 ∂P) ≤ η n + ε) :
    (∫ ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by sorry

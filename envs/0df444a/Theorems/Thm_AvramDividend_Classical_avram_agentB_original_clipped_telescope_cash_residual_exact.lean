-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_original_clipped_telescope_cash_residual_exact
-- name    : AvramDividend.Classical.avram_agentB_original_clipped_telescope_cash_residual_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:14:00.848308+00:00
-- url     : https://prove2.me/theorems/cb077f9e-a271-4ec9-83da-bba6578a8d5e
-- title:
--   Minimal exact physical stopped HJB cash and contact telescope, no stochastic regularity extra assumptions
-- statement:
--   For the original pre-ruin stopping time bounded by n, the positive-clock discounted HJB terminal payoff plus genuine strict original Stieltjes cash, minus w(x) and the original physical prepayment generator-grid sum, equals the initial right-payment contact, intermediate original right-dividend reserve contacts and terminal stopped postpayment correction, plus strict cash. This is a direct algebraic consequence of the existing proved gledger35 four-event telescope, with no Gaussian, jump, or HJB sign assumptions.
-- source:
--   Proved avram_gledger35_original_clipped_uniform_four_event_telescope and deterministic Finset.sum_add_distrib, original X, original D, and original ruinTime; all quantifiers and endpoint conventions coincide.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_agentB_original_clipped_telescope_cash_residual_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (n m : ℕ) (ρ : Ω → ℝ≥0)
    (hρruin : ∀ η, (ρ η : ℝ≥0∞) ≤ ruinTime X x D η)
    (hρbound : ∀ η, ρ η ≤ (n : ℝ≥0))
    (ω : Ω) (hpos : 0 < ρ ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let S : ℝ := Finset.sum (Finset.range (m + 1)) (fun i =>
      (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
        E (v (i + 1)) * (w (Z i) - w (Y (v i))))
    let K : ℝ := (w (x - rightLimit D 0 ω) - w x) +
      Finset.sum (Finset.range (m + 1)) (fun i =>
        E (v (i + 1)) *
          ((w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
            (w (Y (v (i + 1))) - w (riskProcess X x D (v (i + 1)) ω)))) +
      E (ρ ω) * (w (riskProcess X x D (ρ ω) ω) - w (Y (ρ ω)))
    let F : ℝ := (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    (if ρ ω = 0 then w x else E (ρ ω) *
      w (riskProcess X x D (ρ ω) ω) + F) - w x - S = K + F := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_first_size2_ruin_cash_excludes_physical_unitmark_certificate
-- name    : AvramDividend.Classical.avram_jump6_A_actual_first_size2_ruin_cash_excludes_physical_unitmark_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:33:14.318212+00:00
-- url     : https://prove2.me/theorems/102ec163-f67e-4fcf-a98f-7c8c30e268f9
-- title:
--   Actual original finite-cap first-ruin Stieltjes cash contradicts unit-fullmark signed certificate at physical first mark
-- statement:
--   On the genuine original Brownian minus size-two Poisson sample path with first negative mark at the stopped clock σ≤1/10 and Brownian tube amplitude <1/4000, the previously Proved aef35b4c states that the actual original finite-cap barrier payoff, including its right-closed Stieltjes dividend cash, is exactly zero. The original full-mark noise under a true one-mark count equals −2+2σ, while the true HJB candidate w(1/10) + Brownian σ + fullmark is ≤−11/20. Consequently no nonpositive drift can make the original physical signed Ito cash certificate hold on this event. This provides a rigorous original-source stopped-path obstruction without asserting an unproved positive-probability model or server Disproved verdict.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_finitecap_first_size2_ruin_terminal_plus_inclusive_cash_zero
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_unit_fullmark_ruin_gap_scalar_obstruction
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_actual_first_size2_ruin_cash_excludes_physical_unitmark_certificate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ u : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hBefore : ∀ t : ℝ≥0, t < σ → N t = 0)
    (hFirst : N σ = 1)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0)
        (_ : (1 / 5 : ℝ) - (1 / 10 : ℝ) < X.X s ω),
        (s : ℝ≥0∞)))
    (hσsmall : (σ : ℝ) ≤ 1 / 10)
    (q : ℝ) (w : ℝ → ℝ)
    (hw : ∀ z : ℝ, w z =
      if z < 0 then 0 else 1 + z + z ^ 2)
    (H Jfull Drift : ℝ)
    (hH : H =
      Real.exp (-(q * (σ : ℝ))) *
        w (riskProcess X (1 / 10 : ℝ)
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) σ ω) +
        (∫⁻ s in paymentTimes
            (ruinTime X (1 / 10 : ℝ)
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω) ∩
            Iic (σ : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)).toReal)
    (hJ : Jfull = -2 * (N σ : ℝ) + 2 * (σ : ℝ))
    (hDrift : Drift ≤ 0)
    (hLedger : H ≤ w (1 / 10 : ℝ) + B σ + Jfull + Drift) :
    False := by sorry

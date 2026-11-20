-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_finitecap_first_size2_ruin_terminal_plus_inclusive_cash_zero
-- name    : AvramDividend.Classical.avram_jump6_A_actual_finitecap_first_size2_ruin_terminal_plus_inclusive_cash_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:26:59.002173+00:00
-- url     : https://prove2.me/theorems/aef35b4c-3e4f-482f-9d4e-84c561e7c6ec
-- title:
--   The original clipped finite-cap reward vanishes exactly at a physical first size-two ruin mark with no barrier payments
-- statement:
--   On an actual Brownian-size-two-Poisson sample path with a Brownian small tube, no negative mark before σ, at least one mark at σ, and its finite strict upper-exit clock u, the true capped dividend barrier ruinTime equals σ and the exact stopped discounted terminal w(riskProcess) plus the right-closed Stieltjes cash integral is zero at σ. Physical mark ruins the reserve, w vanishes on negative values, and the upper barrier is never crossed during the tube so no discounted dividend was paid. This is the exact stopped payoff event required to connect the positive first mark event to the unit-fullmark signed-ledger contradiction, retaining the original path, stopping and payment conventions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_actual_finitecap_first_size2_ruin_terminal_plus_inclusive_cash_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B : ℝ≥0 → ℝ) (N : ℝ≥0 → ℕ)
    (σ u : ℝ≥0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * (N t : ℝ))
    (hTube : ∀ t : ℝ≥0, t ≤ σ → |B t| < (1 / 4000 : ℝ))
    (hBefore : ∀ t : ℝ≥0, t < σ → N t = 0)
    (hMark : 1 ≤ N σ)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0)
        (_ : (1 / 5 : ℝ) - (1 / 10 : ℝ) < X.X s ω),
        (s : ℝ≥0∞)))
    (w : ℝ → ℝ) (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (q : ℝ) :
    ruinTime X (1 / 10 : ℝ)
      (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω =
        (σ : ℝ≥0∞) ∧
    Real.exp (-(q * (σ : ℝ))) *
      w (riskProcess X (1 / 10 : ℝ)
          (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) σ ω) +
      (∫⁻ s in paymentTimes
          (ruinTime X (1 / 10 : ℝ)
            (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω) ∩
          Iic (σ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure
              (barrierStrategy X (1 / 10 : ℝ) (1 / 5 : ℝ)) ω)).toReal = 0 := by sorry

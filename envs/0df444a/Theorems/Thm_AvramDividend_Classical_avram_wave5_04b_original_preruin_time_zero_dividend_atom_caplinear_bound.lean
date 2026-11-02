-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_time_zero_dividend_atom_caplinear_bound
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_time_zero_dividend_atom_caplinear_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:03:39.487692+00:00
-- url     : https://prove2.me/theorems/dbaf2f36-1c6c-4d58-aa48-bf08bb84b054
-- title:
--   Actual original-source time-zero Stieltjes atom is controlled by the closed-cap value loss
-- statement:
--   For an admissible finite-cap strategy driven by the genuine spectrally negative Levy source, its complete actual dividendMeasure mass at the instant zero (the closed interval [0,0]) is bounded by the decrease of the cap-linear HJB test function across the right-payment at zero. The true D 0 omega = 0 convention and the rightLimit D 0 omega are preserved. Solvency is obtained from admissibility at t=0, and the source is evaluated before right-payment, with no strict-interior localisation, differentiability at zero or c, or purely atomic strategy hypothesis.
-- source:
--   Wave 5 04-B. Proved full-measure closed-horizon bound 885b5e42-8ccb-409e-ac49-48becc2bf389 specialised at T=0 and true source x+X_0, using IsAdmissibleLe initial post-payment solvency.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_caplinear_closed_horizon_all_mass_budget

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_time_zero_dividend_atom_caplinear_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) :
    (∫⁻ t in Icc (0 : ℝ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) ≤
    ENNReal.ofReal (
      (if x + X.X 0 ω ≤ c then w (x + X.X 0 ω)
        else w c + (x + X.X 0 ω - c)) -
      (if x + X.X 0 ω - rightLimit D 0 ω ≤ c
        then w (x + X.X 0 ω - rightLimit D 0 ω)
        else w c + ((x + X.X 0 ω - rightLimit D 0 ω) - c))) := by sorry

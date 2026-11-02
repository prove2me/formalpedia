-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_full_stieltjes_caplinear_budget
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_full_stieltjes_caplinear_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:39:38.810276+00:00
-- url     : https://prove2.me/theorems/bf02d8bd-e937-46f3-8ca6-7c4a83a33899
-- title:
--   Original pre-ruin capped dividend source controls all stopped Stieltjes payments through cap-linear value drop
-- statement:
--   For the actual spectrally negative Levy source path and an admissible finite-cap dividend strategy, at a pre-ruin terminal time including time zero, the full discounted stopped original Stieltjes payout is dominated by the cap-linear HJB value drop at the genuine terminal source value x+X_T, with the terminal right-payment applied after the source value. This includes every diffuse, singular-continuous and atomic dividend, and requires no strict-interior reserve localisation. This source-frozen terminal budget is not the still-required dynamic Ito-Meyer source/control chain rule.
-- source:
--   Original IsAdmissibleLe and IsAdmissible right-jump solvency; proved full closed-horizon Stieltjes budget 899a15ee-29a7-4820-b5c7-d87109a699fe; proved cap-linear secant 420ddace-18e0-48de-aecc-c7ccbc6c7c52; proved dividendStrategy_le_rightLimit 953f0e91-72ae-4c01-a7d6-8c4d19980128. Direct finite-cap original-process control component towards BV verifier ef7e6c20-a118-46f0-ac94-5b02204bba49.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_full_stieltjes_caplinear_budget
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
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (
      (if x + X.X T ω ≤ c then w (x + X.X T ω)
        else w c + (x + X.X T ω - c)) -
      (if x + X.X T ω - rightLimit D T ω ≤ c
        then w (x + X.X T ω - rightLimit D T ω)
        else w c + ((x + X.X T ω - rightLimit D T ω) - c))) := by sorry

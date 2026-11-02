-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_caplinear_closed_horizon_all_mass_budget
-- name    : AvramDividend.Classical.avram_wave5_04b_caplinear_closed_horizon_all_mass_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:36:54.260202+00:00
-- url     : https://prove2.me/theorems/885b5e42-8ccb-409e-ac49-48becc2bf389
-- title:
--   Cap-linear closed-boundary full Stieltjes dividend budget, including all diffuse and right-payment mass
-- statement:
--   For the actual monotone adapted dividend strategy, all discounted Stieltjes payments on a closed horizon, including absolutely continuous dividends, singular-continuous dividends, every right-payment jump and the time-zero atom, are bounded by the value drop of the cap-linear extension of an HJB gradient supersolution. The frozen initial reserve y may exceed the finite positive cap. The only solvency condition is that y covers the entire cumulative dividend through the horizon. This is a deterministic dividend-only budget for source-frozen intervals, not the full Lévy-driven Itô–Meyer control identity.
-- source:
--   Proved full-horizon source Stieltjes measure bound 899a15ee-29a7-4820-b5c7-d87109a699fe; Proved cap-linear full nonnegative secant 420ddace-18e0-48de-aecc-c7ccbc6c7c52; Proved monotone right dividend limit 953f0e91-72ae-4c01-a7d6-8c4d19980128. Source-frozen bridge for Avram Wave 5 BV verification ef7e6c20-a118-46f0-ac94-5b02204bba49.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_caplinear_closed_horizon_all_mass_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (y : ℝ)
    (hyD : rightLimit D T ω ≤ y) :
    (∫⁻ t in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (
      (if y ≤ c then w y else w c + (y - c)) -
      (if y - rightLimit D T ω ≤ c
        then w (y - rightLimit D T ω)
        else w c + ((y - rightLimit D T ω) - c))) := by sorry

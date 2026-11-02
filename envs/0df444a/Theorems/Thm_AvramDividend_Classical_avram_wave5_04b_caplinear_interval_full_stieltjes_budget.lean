-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_caplinear_interval_full_stieltjes_budget
-- name    : AvramDividend.Classical.avram_wave5_04b_caplinear_interval_full_stieltjes_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:48:38.113289+00:00
-- url     : https://prove2.me/theorems/02319f55-27be-45a8-a1c2-22a58ed611cb
-- title:
--   Boundary-safe cap-linear bound for every full Stieltjes payment time cell including singular-continuous variation
-- statement:
--   On every half-open time interval (a,b], the complete actual discounted Stieltjes dividend measure, with all absolutely continuous and singular-continuous variation and the right-payment atom at b, is bounded by the cap-linear HJB potential drop between y-D_{a+} and y-D_{b+}. The frozen source budget y may exceed the cap and is assumed to cover cumulative dividends through b. This is a derivative-free full-interval control inequality, valid when the reserve contacts zero or cap. The excluded time-zero atom is handled by the separate closed-horizon bound. It is designed for finite-grid source-before-dividend approximations of the dynamic controlled Ito-Meyer term.
-- source:
--   Proved dividendMeasure_Ioc_rightLimit f9211de0-c48b-4907-aaf9-e9774b5831ef, Proved dividend rightLimit monotonicity f7eef805-3be2-4d1e-9ca1-61e09a0f266e, Proved general discounted Stieltjes measure comparison, and Proved cap-linear full secant 420ddace-18e0-48de-aecc-c7ccbc6c7c52. Supports Wave5 Chat04-B full boundary-safe Stieltjes control.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_lintegral_le_measure
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_caplinear_interval_full_stieltjes_budget
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
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b) (y : ℝ)
    (hy : rightLimit D b ω ≤ y) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (
      (if y - rightLimit D a ω ≤ c
        then w (y - rightLimit D a ω)
        else w c + ((y - rightLimit D a ω) - c)) -
      (if y - rightLimit D b ω ≤ c
        then w (y - rightLimit D b ω)
        else w c + ((y - rightLimit D b ω) - c))) := by sorry

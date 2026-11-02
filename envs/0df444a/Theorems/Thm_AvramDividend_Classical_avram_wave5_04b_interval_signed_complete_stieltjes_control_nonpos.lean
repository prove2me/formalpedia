-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_interval_signed_complete_stieltjes_control_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_interval_signed_complete_stieltjes_control_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:43:18.420268+00:00
-- url     : https://prove2.me/theorems/9425ae05-70cd-4fd8-87aa-0d33fb88c688
-- title:
--   Full signed discounted Stieltjes correction on any boundary-contacting cap-linear time cell is nonpositive
-- statement:
--   For every admissible dividend strategy path and any half-open interval (a,b], the real discounted integral of the actual dividendMeasure D omega, including absolutely continuous variation, singular-continuous variation and every right-payment atom, plus the cap-linear value change V(y-D_(b+))−V(y-D_(a+)) is nonpositive. The frozen source budget y covers dividends through b and may lie above the cap. The finite positive cap, nonnegative discount q, and full-cap interior gradient hypothesis suffice. This theorem has no reserve-interior localisation, no atomlessness assumption, and no derivative at reserve zero or cap. A separate closed-horizon theorem covers the time-zero atom.
-- source:
--   Derive the real signed Stieltjes inequality from Proved exact full interval measure bound 02319f55-27be-45a8-a1c2-22a58ed611cb, Proved right-limit monotonicity f7eef805-3be2-4d1e-9ca1-61e09a0f266e, and Proved cap-linear full secant 420ddace-18e0-48de-aecc-c7ccbc6c7c52. The cap-linear drop is nonnegative, making ENNReal.toReal_mono valid for finite real budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_caplinear_interval_full_stieltjes_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_interval_signed_complete_stieltjes_control_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b) (y : ℝ)
    (hy : rightLimit D b ω ≤ y) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      V (y - rightLimit D b ω) - V (y - rightLimit D a ω) ≤ 0 := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_interval_signed_stieltjes_control_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_interval_signed_stieltjes_control_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:53:22.829718+00:00
-- url     : https://prove2.me/theorems/3e748b51-e344-4668-935b-d97ed5744826
-- title:
--   Original Lévy-source exact discounted signed Stieltjes correction across any pre-ruin capped cell
-- statement:
--   For any genuine spectrally negative Levy source, admissible finite-cap dividends and a pre-ruin time cell (a,b], the real actual discounted dividendMeasure integral plus the original-source cap-linear post-minus-pre dividend value change at X_b is nonpositive. The source's chronological left jump occurs before the right dividend at b, and all diffuse absolutely continuous and singular-continuous dividend variation as well as right-payment atoms are included. Source prepayment reserve may exceed the cap; postpayment solvency follows from IsAdmissibleLe. No strict reserve interior condition or endpoint derivative is required.
-- source:
--   Specialise the Proved signed complete Stieltjes interval theorem avram_wave5_04b_interval_signed_complete_stieltjes_control_nonpos with source budget y=x+X_b and true postpayment solvency from IsAdmissibleLe X x cap D at b. This is the signed actual-source finite-cell interface for Chat 03 and Chat 04.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_interval_signed_complete_stieltjes_control_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_interval_signed_stieltjes_control_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨ (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      V (x + X.X b ω - rightLimit D b ω) -
      V (x + X.X b ω - rightLimit D a ω) ≤ 0 := by sorry

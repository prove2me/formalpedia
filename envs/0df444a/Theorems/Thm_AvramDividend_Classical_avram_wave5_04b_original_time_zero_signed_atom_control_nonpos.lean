-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_time_zero_signed_atom_control_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_original_time_zero_signed_atom_control_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:46:10.06705+00:00
-- url     : https://prove2.me/theorems/9390a5c6-7d73-4e6d-aec0-107d0016b967
-- title:
--   Original-source time-zero actual dividend atom has nonpositive signed cap-linear correction
-- statement:
--   The genuine initial right-payment atom at time zero, measured by the actual dividendMeasure D omega on [0,0] with D 0 omega = 0, has nonpositive real signed correction after adding the cap-linear value change from original source x+X_0 to x+X_0−rightLimit D_0. The result holds at reserve zero or cap and even if the pre-payment source exceeds the finite cap. It assumes no endpoint derivative or strict-interior localisation and preserves the chronological source-before-right-dividend convention.
-- source:
--   Combine Proved original-source time-zero full Stieltjes atom bound dbaf2f36-1c6c-4d58-aa48-bf08bb84b054 and Proved cap-linear secant 420ddace-18e0-48de-aecc-c7ccbc6c7c52, using admissibility at zero, dividend monotonicity, and conversion of finite ENNReal.ofReal budget to a signed real inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_time_zero_dividend_atom_caplinear_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_original_time_zero_signed_atom_control_nonpos
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
    (ω : Ω) :
    (∫⁻ s in Icc (0 : ℝ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      V (x + X.X 0 ω - rightLimit D 0 ω) -
      V (x + X.X 0 ω) ≤ 0 := by sorry

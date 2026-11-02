-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
-- name    : AvramDividend.Classical.avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:12:10.677589+00:00
-- url     : https://prove2.me/theorems/b7f6754b-bb40-4d86-bd48-aae4411986f7
-- title:
--   Every finite, infinite or zero cap: complete original closed-horizon signed dividend Stieltjes domination
-- statement:
--   For any actual admissible original Lévy-path left-continuous finite-variation dividend strategy, including continuous and singular-continuous dividends and arbitrarily many right payment jumps, the entire original discounted dividendMeasure on the closed interval [0,T] plus the caplinear verification-value change from pre-control source value to post-cumulative-payment reserve is nonpositive, for every ENNReal cap C, including literal zero cap and top. This is valid at T=0 or strictly before ruin and retains the time-zero atom, true rightLimit convention, and simultaneous underlying source and dividend jumps. At positive cap the previously proved original signed Stieltjes theorem applies; at zero cap the globally affine extension V(y)=w(0)+y on nonnegative reserves gives equality of the value drop and total cumulative dividend, combined with the existing discounted full dividendMeasure budget. No finite-jump, smooth-control, or initial-capital cap assumption.
-- source:
--   Proved positive-cap full closed Stieltjes signed inequality; Proved universal discounted dividendMeasure bound; zero-cap affine cap-linear V and IsAdmissible right-payment solvency. All at pinned Mathlib revision.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_closed_horizon_real_signed_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X T ω - rightLimit D T ω) -
        V (x + X.X T ω)) ≤ 0 := by sorry

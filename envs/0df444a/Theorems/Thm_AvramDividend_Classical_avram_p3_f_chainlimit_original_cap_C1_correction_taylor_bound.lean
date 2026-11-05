-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_cap_C1_correction_taylor_bound
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_cap_C1_correction_taylor_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:25:27.353276+00:00
-- url     : https://prove2.me/theorems/1fa6a52e-b7d5-4bd2-8b75-1f9716b27d9b
-- title:
--   Actual original frozen cap-crossing correction bounded by cap C1 Taylor modulus
-- statement:
--   For an actual original Lévy source and right-payment-frozen grid cell, the difference between its cap-pasted V increment and w increment is bounded by the local first-order Taylor error of w at the cap. The cap has smooth-fit slope one, and only above-cap cells require an explicit genuine local C1 Taylor bound. Below-cap and cap-contact cells have zero correction, as does the infinite-cap case. This supplies an exact source-specific analytic estimate to control P3-F's discounted cap crossing sum under P3-G compact-strip hypotheses, without assuming any stopped inequality or generator compensation.
-- source:
--   Proved exact original source frozen cap crossing identity 84f8df8a; source-specific C1 Taylor at finite cap and smooth fit deriv w(C)=1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_frozen_cap_crossing_C1_correction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_cap_C1_correction_taylor_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hSlope : C ≠ ⊤ → deriv w C.toReal = 1)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ ω i, i < n →
      let a := x + X.X (u i) ω - rightLimit D (u i) ω
      let b := x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
      (C ≠ ⊤ → C.toReal < b →
        |w b - w C.toReal - deriv w C.toReal * (b - C.toReal)| ≤
          ε * |b - C.toReal|) →
      |(V b - V a) - (w b - w a)| ≤ ε * |b - C.toReal| := by sorry

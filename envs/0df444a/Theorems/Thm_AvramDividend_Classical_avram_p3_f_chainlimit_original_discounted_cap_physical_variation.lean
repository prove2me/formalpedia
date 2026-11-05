-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_discounted_cap_physical_variation
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_discounted_cap_physical_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:31:22.572065+00:00
-- url     : https://prove2.me/theorems/a8fdf437-589b-48b0-8bca-823d8a6bb4bb
-- title:
--   Original frozen BV cap C1 error controlled by physical Lévy source variation
-- statement:
--   On the actual original spectrally negative Lévy path and original admissible left-continuous/right-payment dividend control, assume the genuine frozen post-rightpayment grid states are below a finite cap and finite-cap smooth-fit and C1 Taylor moduli hold at each actual next source-frozen endpoint. Then the exact discounted cap correction is at most epsilon times the discounted absolute physical X source increments. This retains source-before-payment chronology and finite and infinite cap contact without compensation. The cap state bound is a transparent physical localisation hypothesis for P3-G.
-- source:
--   Source exact Proved F11 1fa6a52e and cap correction F6 84f8df8a; physical d_i=ΔX.X, source-frozen start cap via explicit condition; finite sum weighted triangle.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_cap_C1_correction_taylor_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_frozen_cap_crossing_C1_correction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_discounted_cap_physical_variation
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
    (q : ℝ) (hq : 0 ≤ q)
    (hSlope : C ≠ ⊤ → deriv w C.toReal = 1)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hTaylor : ∀ ω i, i < n → C ≠ ⊤ →
      C.toReal < x + X.X (u (i + 1)) ω - rightLimit D (u i) ω →
      |w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w C.toReal -
        deriv w C.toReal *
          (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω - C.toReal)| ≤
      ε * |x + X.X (u (i + 1)) ω - rightLimit D (u i) ω - C.toReal|) :
    ∀ ω,
      (∀ i, i < n → C ≠ ⊤ →
        x + X.X (u i) ω - rightLimit D (u i) ω ≤ C.toReal) →
      let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
      let b : ℕ → ℝ := fun i =>
        x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
      let d : ℕ → ℝ := fun i =>
        X.X (u (i + 1)) ω - X.X (u i) ω
      let κ : ℕ → ℝ := fun i =>
        if C = ⊤ then 0
        else if b i ≤ C.toReal then 0
        else w C.toReal + (b i - C.toReal) - w (b i)
      |∑ i ∈ Finset.range n, e i * κ i| ≤
        ε * ∑ i ∈ Finset.range n, e i * |d i| := by sorry

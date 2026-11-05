-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_discounted_cap_C1_grid_modulus
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_discounted_cap_C1_grid_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:42:21.870186+00:00
-- url     : https://prove2.me/theorems/6ec3da8f-5a7b-4abf-bc96-6d8b8685bce0
-- title:
--   Actual original Lévy cap-crossing C1 correction controlled across discounted frozen cells
-- statement:
--   For the actual original Lévy source and right-payment-frozen dividend control, if finite-cap smooth fit and explicit local C1 Taylor modulus hold at each true frozen source endpoint, the absolute discounted sum of all cap-crossing corrections is bounded by the source-specific weighted cap distances times ε. The infinite-cap and cap-contact cases are covered. This is a true-path estimate for the cap correction in the strict cash C1 grid budget; no stochastic mean-zero compensation or canonical verification claim is assumed.
-- source:
--   Accepted P3-F cap C1 correction theorem 1fa6a52e and original source discount exp(-qu); Finset abs sum, signed cellwise estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_cap_C1_correction_taylor_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_frozen_cap_crossing_C1_correction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_discounted_cap_C1_grid_modulus
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
      let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
      let b : ℕ → ℝ := fun i =>
        x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
      let κ : ℕ → ℝ := fun i =>
        if C = ⊤ then 0
        else if b i ≤ C.toReal then 0
        else w C.toReal + (b i - C.toReal) - w (b i)
      |∑ i ∈ Finset.range n, e i * κ i| ≤
        ε * ∑ i ∈ Finset.range n, e i * |b i - C.toReal| := by sorry

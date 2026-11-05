-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_discounted_cap_physical_localTaylor
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_discounted_cap_physical_localTaylor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:49:09.858909+00:00
-- url     : https://prove2.me/theorems/53854219-e215-4ab4-a9a2-f95fed59520e
-- title:
--   Pathwise-local original frozen C1 cap correction bounded by actual source variation
-- statement:
--   For a fixed genuine original Lévy sample path and physical right-payment-frozen grid, assume only that path's postpayment starting cells lie within the finite cap and that the actual source-only cap-crossing endpoints obey a pathwise-local C1 Taylor modulus. Then the discounted cap-crossing correction is bounded by epsilon times discounted absolute original X source increments. The local Taylor premise belongs inside the sample path quantifier, allowing P3-G to supply it on a compact stopped strip rather than requiring a global uniform modulus over all sample paths.
-- source:
--   Source exact original F18 accepted cap C1 overhang proof a8fdf437 with legitimate quantifier localisation; accepted F11 1fa6a52e and F6 84f8df8a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_cap_C1_correction_taylor_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_frozen_cap_crossing_C1_correction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_discounted_cap_physical_localTaylor
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
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ ω,
      (hStartCap : ∀ i, i < n → C ≠ ⊤ →
        x + X.X (u i) ω - rightLimit D (u i) ω ≤ C.toReal) →
      (hTaylor : ∀ i, i < n → C ≠ ⊤ →
        C.toReal < x + X.X (u (i + 1)) ω - rightLimit D (u i) ω →
        |w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
          w C.toReal -
          deriv w C.toReal *
            (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω - C.toReal)| ≤
        ε * |x + X.X (u (i + 1)) ω - rightLimit D (u i) ω - C.toReal|) →
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

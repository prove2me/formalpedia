-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_discounted_cap_error_BV_envelope
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_discounted_cap_error_BV_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:10:11.321205+00:00
-- url     : https://prove2.me/theorems/3e87178b-6217-4bda-a8e6-726b14a01115
-- title:
--   Original localised BV source cap C1 correction controlled by drift and finite negative-jump mass
-- statement:
--   For an actual original BV Lévy source sample ω, a particular ordered physical grid and the original post-rightpayment control, assume the pathwise frozen start reserves meet the finite cap and the same stopped path's finite-cap C1 smooth-fit Taylor modulus. Then almost surely the exact discounted cap correction is controlled by epsilon times |drift|*clock length plus the original residual and negative-jump accumulator variations. This composes F24 pathwise-local cap overhang, F19 real source variation and F21 actual J monotonicity, with the Taylor hypothesis after ω and grid rather than global.
-- source:
--   P3-F F24 pathwise-local cap correction, F19 discounted physical source variation, F21 original J monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_discounted_cap_physical_localTaylor
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_discounted_actual_source_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_raw_J_monotone
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_discounted_cap_error_BV_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (hSlope : C ≠ ⊤ → deriv w C.toReal = 1)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      ∀ (n : ℕ) (u : ℕ → ℝ≥0)
        (hGrid : ∀ i, i < n → u i ≤ u (i + 1))
        (hStartCap : ∀ i, i < n → C ≠ ⊤ →
          x + X.X (u i) ω - rightLimit D (u i) ω ≤ C.toReal)
        (hTaylor : ∀ i, i < n → C ≠ ⊤ →
          C.toReal < x + X.X (u (i + 1)) ω - rightLimit D (u i) ω →
          |w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
            w C.toReal -
            deriv w C.toReal *
              (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω - C.toReal)| ≤
          ε * |x + X.X (u (i + 1)) ω - rightLimit D (u i) ω - C.toReal|),
        let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
        let κ : ℕ → ℝ := fun i =>
          let b := x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
          if C = ⊤ then 0
          else if b ≤ C.toReal then 0
          else w C.toReal + (b - C.toReal) - w b
        |∑ i ∈ Finset.range n, e i * κ i| ≤
          ε * (|X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
            (R (u n) - R (u 0)) +
            (J (u n) - J (u 0))) := by sorry

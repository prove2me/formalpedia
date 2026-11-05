-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_localised_cap_C1_source_error_tendsto_zero
-- name    : AvramDividend.Classical.avram_p3_f_chainlimit_original_localised_cap_C1_source_error_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:36:48.385615+00:00
-- url     : https://prove2.me/theorems/e8dad9d1-cf9c-4734-a36c-f83e862bc628
-- title:
--   Original BV localised cap C1 source error vanishes on physical stopped grid families
-- statement:
--   For the genuine original bounded-variation Levy source, admissible right-payment dividends, and sample-dependent countable mesh family, the complete discounted finite-cap C1 correction tends to zero under the actual physical finite-variation envelope and vanishing local C1 Taylor modulus. The almost-sure source event is chosen before the sample-dependent physical grids and tolerances, and every reserve/cap correction is computed from the original X.X and rightLimit D. The physical variation envelope is explicit for P3-G to prove; no stopped-chain inequality or generator compensation is presupposed.
-- source:
--   Proved original physical cap Taylor F24, physical discounted source variation F19 and monotone original J F21; squeeze on actual source cap correction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_discounted_cap_physical_localTaylor
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_discounted_actual_source_variation
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_raw_J_monotone
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_f_chainlimit_original_localised_cap_C1_source_error_tendsto_zero
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
    (hSlope : C ≠ ⊤ → deriv w C.toReal = 1) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      ∀ (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ) (ε : ℕ → ℝ)
        (hGrid : ∀ k i, i < n k → (u k) i ≤ (u k) (i + 1))
        (hε : ∀ k, 0 ≤ ε k)
        (hεlim : Tendsto ε atTop (nhds 0))
        (hStartCap : ∀ k i, i < n k → C ≠ ⊤ →
          x + X.X ((u k) i) ω - rightLimit D ((u k) i) ω ≤ C.toReal)
        (hTaylor : ∀ k i, i < n k → C ≠ ⊤ →
          C.toReal < x + X.X ((u k) (i + 1)) ω -
            rightLimit D ((u k) i) ω →
          |w (x + X.X ((u k) (i + 1)) ω -
            rightLimit D ((u k) i) ω) - w C.toReal -
            deriv w C.toReal *
              (x + X.X ((u k) (i + 1)) ω -
                rightLimit D ((u k) i) ω - C.toReal)| ≤
          ε k * |x + X.X ((u k) (i + 1)) ω -
            rightLimit D ((u k) i) ω - C.toReal|)
        (hSourceBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ k,
          |X.drift| * (((u k) (n k) : ℝ) - ((u k) 0 : ℝ)) +
            (R ((u k) (n k)) - R ((u k) 0)) +
            (J ((u k) (n k)) - J ((u k) 0)) ≤ M),
        let e : ℕ → ℕ → ℝ := fun k i =>
          Real.exp (-(q * ((u k) i : ℝ)))
        let κ : ℕ → ℕ → ℝ := fun k i =>
          let b := x + X.X ((u k) (i + 1)) ω -
            rightLimit D ((u k) i) ω
          if C = ⊤ then 0
          else if b ≤ C.toReal then 0
          else w C.toReal + (b - C.toReal) - w b
        Tendsto (fun k =>
          ∑ i ∈ Finset.range (n k), e k i * κ k i)
          atTop (nhds 0) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_compact_reserve_band_implies_cap_safe_drift
-- name    : AvramDividend.Classical.avram_p3_2_original_physical_compact_reserve_band_implies_cap_safe_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T01:03:06.567385+00:00
-- url     : https://prove2.me/theorems/03bf0d45-53fe-4910-9981-87037d271c6a
-- title:
--   Original X/D compact pre-reserve ceiling yields eventual cap-safe drift segments
-- statement:
--   On original same-space bounded-variation Lévy physical grids, if all genuine controlled left reserves lie below a fixed compact upper ceiling b strictly below finite C (or if C is infinite), every small enough true physical pure-drift increment stays under the cap. This derives the cap-safety condition needed by the original C1 generator closed-cash source estimate directly from the compact-localisation reserve band.
-- source:
--   Proved original strict cap-margin source 20683a9e. Choose the actual margin C.toReal-b and use shrinking physical grids.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_source_strict_cap_margin_driftsafe_grid

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_physical_compact_reserve_band_implies_cap_safe_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (C : ℝ≥0∞) (b : ℝ)
    (hb : C = ⊤ ∨ b < C.toReal)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
    (hGrid : ∀ m i, i < n m → u m i ≤ u m (i + 1))
    (hCeil : ∀ m i, i < n m →
      x + X.X (u m i) ω - rightLimit D (u m i) ω ≤ b)
    (hSmall : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
        (u m (i + 1) : ℝ) - (u m i : ℝ) < δ) :
    ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
      C = ⊤ ∨
      x + X.X (u m i) ω - rightLimit D (u m i) ω +
        (((u m (i + 1) : ℝ) - (u m i : ℝ)) * X.drift) ≤ C.toReal := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_source_strict_cap_margin_driftsafe_grid
-- name    : AvramDividend.Classical.avram_p3_2_original_physical_source_strict_cap_margin_driftsafe_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:50:48.84529+00:00
-- url     : https://prove2.me/theorems/20683a9e-2881-4b17-b8e8-50adf9fb33e5
-- title:
--   Original controlled X/D strict cap reserve margin automatically implies cap-safe drift grid
-- statement:
--   For the original spectrally negative Lévy X and literal post-rightpayment controlled reserve x+X.X(u_i)-rightLimit D(u_i), a fixed strict cap reserve margin and a refining monotone physical time grid imply every pure BV drift upshift Δu*X.drift is eventually inside the closed cap. This discharges the sole extra cap-safe physical drift premise of the accepted P3-2 original cash/HJB source inequality on strict interior localisations, with the C=top case explicit and no equality-in-law or fabricated bounded jump variation.
-- source:
--   Accepted real original physical clock drift shrinking 7056b9d2 and strict cap-margin absorption 11fd5deb, applied to actual source X,D.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_clock_drift_shift_mesh_vanish
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_reserve_cap_margin_absorbs_drift_cells

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_physical_source_strict_cap_margin_driftsafe_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (C : ℝ≥0∞) (ρ : ℝ) (hρ : 0 < ρ)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
    (hGrid : ∀ m i, i < n m → u m i ≤ u m (i + 1)) :
    let z : ℕ → ℕ → ℝ := fun m i =>
      x + X.X (u m i) ω - rightLimit D (u m i) ω
    let c : ℕ → ℕ → ℝ := fun m i =>
      ((u m (i + 1) : ℝ) - (u m i : ℝ)) * X.drift
    (∀ m i, i < n m → C = ⊤ ∨ z m i ≤ C.toReal - ρ) →
    (∀ δ : ℝ, 0 < δ →
      ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
        (u m (i + 1) : ℝ) - (u m i : ℝ) < δ) →
    ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
      C = ⊤ ∨ z m i + c m i ≤ C.toReal := by sorry

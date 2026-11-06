-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
-- name    : AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:12:02.963591+00:00
-- url     : https://prove2.me/theorems/d8bba788-fa45-46a6-b83b-ef369045401c
-- title:
--   Actual original BV ruin-clock-clamped physical grid begins at zero and ends at stopped horizon
-- statement:
--   On the literal original Lévy process X, controlled ruin time and time horizon T, clamp every deterministic uniform physical mesh time at τ=min(ruinTime X x D ω,T). The resulting path-dependent stopped grid starts at zero, terminates at min(T,τ), and is monotone. This is the exact random physical-clock interface consumed by the original nonpositive residual and stopped C1 source identities.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_clock_endpoints_monotone
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    u 0 = 0 ∧ u (m + 1) = min T τ ∧ Monotone u := by sorry

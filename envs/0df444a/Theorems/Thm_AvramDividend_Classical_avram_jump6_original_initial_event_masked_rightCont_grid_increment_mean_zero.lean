-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_original_initial_event_masked_rightCont_grid_increment_mean_zero
-- name    : AvramDividend.Classical.avram_jump6_original_initial_event_masked_rightCont_grid_increment_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T20:43:36.687969+00:00
-- url     : https://prove2.me/theorems/bd8c00d2-5d37-4e93-bac7-a7d10bd3bb9a
-- title:
--   Actual original right-continuous time-zero event-masked stopped predictable Lévy grid increment has zero mean
-- statement:
--   For the exact original spectrally negative Lévy process, its right-continuous natural working filtration and any measurable initial event A in F^+_0, show that the stopped predictable coefficient on a finite physical grid cell multiplied by the original future Lévy increment centered by its true mean has zero expectation after masking by A. The initial-event mask is measurable at every right-continuous grid time because F^+_0 is included in F^+_s. Preserve the same original X by using the Proved right-continuous Lévy lift. This provides genuine event-restricted first-order martingale cancellation needed to bound the original Avram stopped reward on {τ≠0}, rather than merely an unconditional mean-zero statement.
-- source:
--   Original finite/infinite-activity expected positive clock budgets 15815eff, 464200c8. Proved source-rightCont lift e58a099d-9977-4265-9e76-7a5f0f6aa758 and original stopped grid mean zero 00d9de67-d50a-4e9d-95d7-4c63a2180ac3. Canonical initial event A={τ≠0} measurable at F^+_0 by Proved bce62e25-5d97-4357-a119-bc3b8c8eeaa9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_stopped_predictable_gridcell_centered_X_L1_zero
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_jump6_original_initial_event_masked_rightCont_grid_increment_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω)
    (hA : MeasurableSet[𝓕.rightCont 0] A)
    (grid : ℕ → ℝ≥0) (i : ℕ)
    (hGrid : grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ)
    (hHPast : Measurable[(𝓕.rightCont) (grid i)] (H i))
    (hHI : Integrable (H i) P)
    (hXI : Integrable (X.X (grid (i + 1) - grid i)) P) :
    (∫ ω, (if ω ∈ A then H i ω else 0) *
      (X.X (grid (i + 1)) ω - X.X (grid i) ω -
        (∫ η, X.X (grid (i + 1) - grid i) η ∂P)) ∂P) = 0 := by sorry

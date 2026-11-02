-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_original_measurable_jump_enumeration
-- name    : AvramDividend.Classical.avram_wave5_02a_actual_original_measurable_jump_enumeration
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:57:54.956091+00:00
-- url     : https://prove2.me/theorems/c120c3c4-9fc8-461a-9874-dcd71ff382b0
-- title:
--   Every actual original Levy path has one measurable distinct enumeration of its jumps
-- statement:
--   Construct a countable family of measurable original-sample time selectors and measurable active sets such that, simultaneously for every sample, the active times are precisely all positive-time nonzero original process jumps and no active jump is repeated. There are no standard Borel assumptions on the sample space, no Poisson copy, and no bounded-variation or finite-activity restriction.
-- source:
--   Proved original rational-grid first-crossing coverage d2b50fa0 and first-occurrence filtering 73db8e42, with a dense time grid and a surjective enumeration of grid-start rational-level pairs.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_rational_grid_actual_jump_coverage
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_first_candidate_filter_covers_original_jumps

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02a_actual_original_measurable_jump_enumeration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ (T : ℕ → Ω → ℝ≥0) (A : ℕ → Set Ω),
      (∀ n, Measurable (T n)) ∧ (∀ n, MeasurableSet (A n)) ∧
      (∀ ω n, ω ∈ A n → 0 < T n ω ∧
        X.X (T n ω) ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) (T n ω) ≠ 0) ∧
      (∀ ω n m, ω ∈ A n → ω ∈ A m → T n ω = T m ω → n = m) ∧
      (∀ ω u, 0 < u →
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 →
        ∃ n, ω ∈ A n ∧ T n ω = u) := by sorry

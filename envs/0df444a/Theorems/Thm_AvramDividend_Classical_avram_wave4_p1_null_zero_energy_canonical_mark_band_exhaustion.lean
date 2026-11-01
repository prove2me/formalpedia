-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_null_zero_energy_canonical_mark_band_exhaustion
-- name    : AvramDividend.Classical.avram_wave4_p1_null_zero_energy_canonical_mark_band_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:37:43.917942+00:00
-- url     : https://prove2.me/theorems/05542026-f56e-4a22-80e2-efb8f0192ebc
-- title:
--   Literal finite-rate Lévy mark exhaustion that retains the zero mark of ν-measure zero
-- statement:
--   For a ν-integrable nonnegative mark square-envelope g that may vanish on a ν-null set (e.g. the Lévy zero mark), the explicit bands B_n={1/n≤g}∪{g=0} are measurable, increasing, finite ν-measure, and literally exhaust all marks. Unlike a positive-on-E theorem, it can be applied on the original ℝ jump-mark space without replacing the process by a different sample law or excluding z=0 by a new subtype. Finite ν(B_n) follows from the Proved energy threshold lemma plus ν{g=0}=0; coverage uses the pinned reciprocal-natural limit. No Campbell identity or martingale assumption.
-- source:
--   P1 positive-energy threshold finite mark intensity 401645c2 Proved; pinned Mathlib measurableSet_eq, measure_union_le, ENNReal.inv_le_inv', tendsto_inv_nat_nhds_zero.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_positive_square_energy_threshold_finite_mark_intensity

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_null_zero_energy_canonical_mark_band_exhaustion
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (g : E → ℝ≥0∞) (hg : Measurable g)
    (henergy : ∫⁻ z, g z ∂ν < ∞)
    (hzero_null : ν {z | g z = 0} = 0) :
    let B : ℕ → Set E := fun n =>
      {z | (n : ℝ≥0∞)⁻¹ ≤ g z} ∪ {z | g z = 0}
    (∀ n, MeasurableSet (B n)) ∧
    (∀ n, ν (B n) < ∞) ∧
    Monotone B ∧
    (⋃ n, B n) = Set.univ := by sorry

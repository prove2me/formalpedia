-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b189_original_true_random_grid_marked_count_measurable_from_jump_events
-- name    : AvramDividend.Classical.avram_b189_original_true_random_grid_marked_count_measurable_from_jump_events
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:42:51.066441+00:00
-- url     : https://prove2.me/theorems/9f29fb58-7a1f-495d-b4be-875f3a151d4c
-- title:
--   Canonical genuinely jump-containing original finite physical random stopped-grid cell cardinal is measurable
-- statement:
--   For the actual original spectrally negative Lévy source and any finite grid of possibly random physical clock intervals with measurable and ordered endpoints, select the exact physically marked index Finset consisting of the cells containing at least one genuine original source nonzero left-limit jump. The real cardinal of this physically marked Finset is measurable on the original sample space. Prepared B188 proves that the actual physical source jump-containing event for each random interval is measurable, using already Proved negative Poisson cutoff count measurability and true source cutoff exhaustion. The indicator for each such event is therefore measurable, so its sum across finite grid cells is measurable. That sum equals the real cardinal of the genuine source marked-grid Finset. This is a short direct route to the major hJmeas input of the Proved B150 and pending B157 original stopped Gaussian-negative mark finite-mesh energy, bypassing generic B178 and large B180 source assemblies. Publication awaits B188 Proved.
-- source:
--   Prepared B188 original physical random-clock source jump event measurability and Mathlib Finset.measurable_sum and Measurable.ite.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b188_original_random_physical_interval_actual_jump_event_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual original jump-containing cell count of any finite physical stopped grid with ordered measurable random endpoints is a measurable real random variable. -/

theorem AvramDividend.Classical.avram_b189_original_true_random_grid_marked_count_measurable_from_jump_events
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hs : ∀ i, Measurable (s i)) (ht : ∀ i, Measurable (t i))
    (hst : ∀ ω i, s i ω ≤ t i ω) :
    let J : Ω → Finset ℕ := fun ω =>
      S.filter (fun i => ∃ u : ℝ≥0,
        s i ω < u ∧ u ≤ t i ω ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    Measurable (fun ω => ((J ω).card : ℝ)) := by sorry

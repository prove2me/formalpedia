-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b188_original_random_physical_interval_actual_jump_event_measurable
-- name    : AvramDividend.Classical.avram_b188_original_random_physical_interval_actual_jump_event_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T23:27:58.141603+00:00
-- url     : https://prove2.me/theorems/e1e008fe-30bb-4923-acae-bb3798f536d3
-- title:
--   Event of a genuine original source jump between arbitrary measurable random physical clock endpoints is measurable
-- statement:
--   For the actual original spectrally negative Levy process and any ordered physical time interval with measurable possibly random left and right clock endpoints, the event that the original source has at least one nonzero left-limit jump strictly after the left endpoint and up to the right endpoint is measurable. Already Proved jump_phys13 makes the mapped original Poisson count in every reciprocal negative-band rectangle of that random interval measurable, so the event that some such original band count is nonzero is a countable union of measurable events. Already Proved B118 guarantees that any genuine original nonzero jump lies in some finite reciprocal negative-band cutoff, and pending B179 proves that the corresponding original Poisson count is nonzero exactly when such a physical band mark exists. These establish a pointwise event equivalence and hence measurability. The conclusion provides a true original random-clock physical source jump-contact event for stopped Ito mesh classification, with no deterministic clock or artificial Gaussian source assumption. Publication waits for B179 Proved.
-- source:
--   Proved original jump_phys13 random interval negative band source count measurability and B118 common physical cutoff, pending B179 source count to physical band mark equivalence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b118_original_finite_physically_marked_cells_one_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_b179_original_actual_negative_band_source_jump_iff_poisson_count_nonzero
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the genuine spectrally negative Levy sample path, the event of an actual nonzero source jump in any half-open interval between measurable random clocks is measurable. -/

theorem AvramDividend.Classical.avram_b188_original_random_physical_interval_actual_jump_event_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : Ω → ℝ≥0)
    (hs : Measurable s) (ht : Measurable t)
    (hst : ∀ ω, s ω ≤ t ω) :
    MeasurableSet {ω : Ω | ∃ u : ℝ≥0,
      s ω < u ∧ u ≤ t ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} := by sorry

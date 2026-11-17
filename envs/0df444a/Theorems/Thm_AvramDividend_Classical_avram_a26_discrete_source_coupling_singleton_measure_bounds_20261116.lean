-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_discrete_source_coupling_singleton_measure_bounds_20261116
-- name    : AvramDividend.Classical.avram_a26_discrete_source_coupling_singleton_measure_bounds_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:55:40.987577+00:00
-- url     : https://prove2.me/theorems/091c6808-6122-4294-ba18-1bdf61051743
-- title:
--   Source-preserving coupling controls singleton laws by the event of count disagreement
-- statement:
--   For any two measurable natural-valued random variables on the same probability or measure space, their singleton event masses differ in either direction by at most the measure of the event where the variables disagree. Prove by elementary event containment and subadditivity. This transfers original physical-count versus occupied-binomial-grid coupling errors to one-point laws without constructing an alternative probability space.
-- source:
--   Measure monotonicity, finite-union subadditivity; elementary source-space coupling estimate.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a26_discrete_source_coupling_singleton_measure_bounds_20261116
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K Z : Ω → ℕ) (hK : Measurable K) (hZ : Measurable Z)
    (k : ℕ) :
    P.map K {k} ≤ P.map Z {k} + P {ω | K ω ≠ Z ω} ∧
    P.map Z {k} ≤ P.map K {k} + P {ω | K ω ≠ Z ω} := by sorry

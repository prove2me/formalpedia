-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:54:32.203271+00:00
-- url     : https://prove2.me/theorems/52f0bc5f-fb6d-4e4c-95a7-20b6fc1c8835
-- title:
--   Every original BV or UBV Lévy path has finitely many jumps of size at least delta on compact time horizons
-- statement:
--   For any original SpectrallyNegativeLevy P 𝓕 sample ω, finite horizon T and strictly positive mark-size cutoff δ, the literal actual source jump-time set {u∈(0,T] : |X_u(ω)−X_{u−}(ω)|≥δ} is finite. Holds pathwise for every ω with no finite-activity, BV, sigma-finite probability-space extension or marked-Poisson law assumption. Consequently each compact-time source jump-count restriction to a negative mark band separated from zero is finite, including UBV, supplying the genuinely missing local-finiteness prerequisite for marked compensator localisation.
-- source:
--   Proved original-path one-sided jumpmark tendsto results; pinned Set.Infinite.exists_accPt_of_subset_isCompact, accPt_iff_nhds, mem_nhdsWithin_iff_exists_mem_nhds_inter and compact Icc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jumpmark_vanish_from_left
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jumpmark_vanish_from_right
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    {u : ℝ≥0 |
      0 < u ∧ u ≤ T ∧
      δ ≤ dist (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) 0}.Finite := by sorry

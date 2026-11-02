-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero
-- name    : AvramDividend.Classical.avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:05:48.539958+00:00
-- url     : https://prove2.me/theorems/0a9afdb9-4d96-45fb-998e-d7a78f798a44
-- title:
--   Actual original marked Lévy jump measure is globally concentrated on strictly negative marks
-- statement:
--   For every actual SpectrallyNegativeLevy P 𝓕 sample path ω, its genuine intrinsic marked counting measure assigns zero mass to all positive-time marks in [0,∞), globally in the entire time axis, without finite-horizon, bounded-variation, or almost-everywhere assumptions. Uses the actual pathwise Borel counting identity and the source's pathwise nonpositive jump-mark theorem.
-- source:
--   Proved same-path arbitrary-Borel marked counting identity 2c942e8f and Proved original path nonpositive jump marks e95fe5bc; no detached Poisson model or compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_jump_measure_arbitrary_borel_count_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Set.univ ×ˢ Ici (0 : ℝ)) = 0 := by sorry

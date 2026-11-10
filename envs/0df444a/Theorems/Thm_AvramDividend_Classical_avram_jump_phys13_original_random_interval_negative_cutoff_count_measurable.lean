-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
-- name    : AvramDividend.Classical.avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:23:03.398276+00:00
-- url     : https://prove2.me/theorems/c20912c8-7e6c-4f6c-b4c5-b93716523540
-- title:
--   Actual original negative-jump count over random physical half-open endpoints is measurable
-- statement:
--   For the original X.X jump measure on its original probability space, the negative-cutoff marked count in a half-open interval whose endpoints depend measurably on the sample ω is measurable. The original source already possesses a proved s-finite kernel on the same Ω, and the random-interval event is a measurable subset of Ω times the physical time-mark space. This removes the measurable-source premise for fixed-band physical terminal-cell counts without assuming independent stopping or finite variation.
-- source:
--   PJ-PHYS13 supporting exact original physical L1 final-cell source for 0b1a879a, extending public Proved 17e97019 and a5c5c5b5; uses Proved eb357d08 original kernel.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (cut : ℕ) (τ e : Ω → ℝ≥0)
    (hτ : Measurable τ) (he : Measurable e) :
    Measurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (τ ω) (e ω) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))) := by sorry

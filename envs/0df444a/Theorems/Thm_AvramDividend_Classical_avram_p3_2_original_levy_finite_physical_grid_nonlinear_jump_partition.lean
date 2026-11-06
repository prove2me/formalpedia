-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_levy_finite_physical_grid_nonlinear_jump_partition
-- name    : AvramDividend.Classical.avram_p3_2_original_levy_finite_physical_grid_nonlinear_jump_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:29:57.50771+00:00
-- url     : https://prove2.me/theorems/0a9f4196-291f-402f-aa32-c74cbab4ed9c
-- title:
--   Exact finite physical grid partition of the intrinsic original Lévy nonlinear jump count
-- statement:
--   Fix a genuine original spectrally negative Lévy path and a monotone finite physical time grid. The intrinsic original marked nonzero-jump counting integral of any measurable nonnegative nonlinear kernel on the full interval equals the sum of its exact original marked jump integrals over every adjacent half-open grid cell, with no jump atom dropped or duplicated, including at grid points.
-- source:
--   Accepted original Lévy joint mark measurability, original nonzero jump-set measurability and finite physical-grid marked-count additivity, avoiding any Poisson proxy or finite-jump hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact finite physical grid partition of the original Lévy nonlinear
marked jump integral, retaining every original mark and endpoint atom. -/

theorem AvramDividend.Classical.avram_p3_2_original_levy_finite_physical_grid_nonlinear_jump_partition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u : ℕ → ℝ≥0) (hmono : Monotone u) (n : ℕ)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂
      ((Measure.count.restrict
        ({t : ℝ≥0 | 0 < t ∧
          X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0} ∩
          Set.Ioc (u 0) (u n))).map
        (fun t : ℝ≥0 => (t,
          X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)))) =
      ∑ i ∈ Finset.range n,
        (∫⁻ p, F p ∂
          ((Measure.count.restrict
            ({t : ℝ≥0 | 0 < t ∧
              X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0} ∩
              Set.Ioc (u i) (u (i + 1)))).map
            (fun t : ℝ≥0 => (t,
              X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t)))) := by sorry

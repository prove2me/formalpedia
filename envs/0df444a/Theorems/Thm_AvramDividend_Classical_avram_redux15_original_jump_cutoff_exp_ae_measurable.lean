-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux15_original_jump_cutoff_exp_ae_measurable
-- name    : AvramDividend.Classical.avram_redux15_original_jump_cutoff_exp_ae_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T11:15:08.635439+00:00
-- url     : https://prove2.me/theorems/b03b6ef4-b8e5-4818-8431-974640acd8b5
-- title:
--   Original finite-cutoff jump exponentials are measurable on the physical probability space
-- statement:
--   For each integer horizon and reciprocal positive cutoff, the exponential of the actual original-path negative-jump magnitude sum over times before the horizon and marks above the cutoff is almost everywhere strongly measurable under the physical probability P. Use original càdlàg jump-time measurability and finite large-jump marks.
-- source:
--   Authentic original BV negative-jump cutoff functionals; same integrand as avram_redux13_original_jump_cutoff_transform_tendsto.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_redux15_original_jump_cutoff_exp_ae_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ (n k : ℕ),
      AEStronglyMeasurable (fun ω : Ω => Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) < (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal))) P := by sorry

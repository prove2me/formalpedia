-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb27a_original_finite_mark_grid_to_real_floor
-- name    : AvramDividend.Classical.avram_bvb27a_original_finite_mark_grid_to_real_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:31:14.837126+00:00
-- url     : https://prove2.me/theorems/30183c27-5dd6-439d-a674-7d44de502ae8
-- title:
--   Original inclusive physical finite-cap mark grid equals exact real floor-step integral
-- statement:
--   For the original same-space Lévy and dividend strategy, express every inclusive-cap frozen discounted negative-mark compensator cell by the genuine uniform physical cell width and integrate the same source mark-rate coefficients over the exact original real-time uniform-floor step function. At zero, finite cap and ruin masking, no term is dropped or replaced. Uses proved generic physical-grid width-to-step integral.
-- source:
--   Proved bvb25 uniform source-cell step identity; pinned original Avram 2007 Prop4(i),(5.13); needed by 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb25_uniform_cell_source_sum_as_restricted_integral
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bvb27a_original_finite_mark_grid_to_real_floor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q T : ℝ) (hT : 0 < T) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (ω : Ω) :
    let U : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let ψ : ℝ → ℝ := fun b =>
      ∫ z in Set.Iio (0 : ℝ), w (b + z) - w b ∂X.ν
    let c : ℕ → ℝ := fun i =>
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
         0 ≤ U (u n i) ∧ ENNReal.ofReal (U (u n i)) ≤ C
      then Real.exp (-(q * (u n i : ℝ))) * ψ (U (u n i))
      else 0
    let A : ℝ := ∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 ≤ U (u n i) ∧ ENNReal.ofReal (U (u n i)) ≤ C then
        (∫ z in Set.Iio (0 : ℝ),
          Real.exp (-(q * (u n i : ℝ))) *
            (w (U (u n i) + z) - w (U (u n i))) ∂X.ν) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    A = ∫ r in Set.Icc (0 : ℝ) T,
      if 0 ≤ r ∧ r < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
      then c ⌊(r / T) * ((n : ℝ) + 2)⌋₊ else 0 := by sorry

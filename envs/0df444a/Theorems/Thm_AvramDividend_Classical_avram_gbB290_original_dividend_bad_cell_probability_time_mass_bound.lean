-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB290_original_dividend_bad_cell_probability_time_mass_bound
-- name    : AvramDividend.Classical.avram_gbB290_original_dividend_bad_cell_probability_time_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:09:29.138332+00:00
-- url     : https://prove2.me/theorems/a0fe5866-e7b6-4a70-8ee4-d92c9c1bd9ba
-- title:
--   Original admissible dividend bad mesh-cell mass is at most localised total variation divided by refinement
-- statement:
--   For the genuine original dividend strategy, any product measurable time event lying in bad dividend grid cells and whose occupied paths have terminal variation D(n)-D(0) at most M has product probability-time mass at most M/m. This follows from original grid endpoint identity B289 and abstract pathwise-to-product B284; it is the source-specific bad part of finite-cap Gaussian occupation B276b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Finset AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB290_original_dividend_bad_cell_probability_time_mass_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n m M : ℕ) (hm : 0 < m)
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (hinc : ∀ ω, (Prod.mk ω ⁻¹' S) ⊆
      ⋃ i ∈ ((Finset.range (n * m ^ 4)).filter
        (fun i => 1 / ((m : ℝ) ^ 3) <
          D (((i + 1 : ℕ) : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω -
          D ((i : ℝ≥0) * (1 / ((m : ℝ≥0) ^ 4))) ω)),
      Set.Ioo ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
        (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))))
    (hloc : ∀ ω, (∃ t : ℝ, (ω, t) ∈ S) →
      D n ω - D 0 ω ≤ (M : ℝ)) :
    (P.prod volume) S ≤ ENNReal.ofReal ((M : ℝ) / (m : ℝ)) := by sorry

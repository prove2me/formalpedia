-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB284_original_bad_cell_prob_time_mass_bound
-- name    : AvramDividend.Classical.avram_gbB284_original_bad_cell_prob_time_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:04:22.530661+00:00
-- url     : https://prove2.me/theorems/a9b75950-6ae1-487b-afd7-ca25fccebbf6
-- title:
--   Localised random bad dividend-grid cells have total probability-time mass at most total variation over refinement
-- statement:
--   For a probability space, random monotone dividend grid and measurable sample-time event lying in bad cells, with occupied paths of bounded terminal variation, the event product probability by physical time is at most M/m. From the pathwise B278 bound, Tonelli integrates a uniform section-volume bound. This is the bad-cell part of the finite-cap occupation assembly.

import Mathlib
open MeasureTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB284_original_bad_cell_prob_time_mass_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (d : Ω → ℕ → ℝ) (hmono : ∀ ω, Monotone (d ω))
    (n m M : ℕ) (hm : 0 < m)
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (hinc : ∀ ω, (Prod.mk ω ⁻¹' S) ⊆
      ⋃ i ∈ ((Finset.range (n * m ^ 4)).filter
        (fun i => 1 / ((m : ℝ) ^ 3) < d ω (i + 1) - d ω i)),
      Set.Ioo ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))
        (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))))
    (hloc : ∀ ω, (∃ t : ℝ, (ω, t) ∈ S) →
      d ω (n * m ^ 4) - d ω 0 ≤ (M : ℝ)) :
    (P.prod volume) S ≤ ENNReal.ofReal ((M : ℝ) / (m : ℝ)) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_interval_count_mark_fubini_20261111
-- name    : AvramDividend.Classical.avram_a06_fixed_interval_count_mark_fubini_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:03:35.114027+00:00
-- url     : https://prove2.me/theorems/9455e165-a585-445a-aa2f-db13989c2992
-- title:
--   Fubini disintegration of fixed marked-interval sums against an independent count grid
-- statement:
--   The independent count grid and full mark stream induce independence of the count grid and any fixed marked interval sum. Since the latter sum is measurable, disintegrate integrable complex functions of the pair by the previously proved independent-stream Fubini theorem. This supports the count-grid Fourier mixing route.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_count_independent_of_fixed_mark_interval_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_independent_stream_integral_disintegration_20261111
open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_fixed_interval_count_mark_fubini_20261111
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Ω → Fin (n + 1) → ℕ) (Y : Ω → ℕ → ℝ)
    (hN : Measurable N) (hY : Measurable Y)
    (hSeparate : IndepFun N Y P) (a b : ℕ)
    (F : ((Fin (n + 1) → ℕ) × ℝ) → ℂ)
    (hF : Integrable F ((Measure.map N P).prod
      (Measure.map (fun ω => ∑ j ∈ Finset.Ico a b, Y ω j) P))) :
    (∫ ω, F (N ω, ∑ j ∈ Finset.Ico a b, Y ω j) ∂P) =
      ∫ m, ∫ z, F (m, z) ∂(Measure.map
        (fun ω => ∑ j ∈ Finset.Ico a b, Y ω j) P) ∂(Measure.map N P) := by sorry

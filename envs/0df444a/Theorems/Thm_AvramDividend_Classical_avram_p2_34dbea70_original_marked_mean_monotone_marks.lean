-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_marked_mean_monotone_marks
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_marked_mean_monotone_marks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:51:12.704941+00:00
-- url     : https://prove2.me/theorems/18fe6f21-9e2d-47d1-926f-d8b5e0c4eb53
-- title:
--   Actual original marked-jump expected count is monotone under mark-set inclusion
-- statement:
--   For the literal original spectrally negative Levy process intrinsic jump count, if mark set B is contained in C, then the ENNReal expected count over (0,T] times B is at most that over (0,T] times C. No alternate process, compensator, or Levy intensity assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_original_marked_mean_monotone_marks {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B C : Set ℝ) (hBC : B ⊆ C) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) ≤
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ C) ∂P) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_integer_time_uniform_mark_mean_measure
-- name    : AvramDividend.Classical.avram_p2_d_future_integer_time_uniform_mark_mean_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:35:30.096205+00:00
-- url     : https://prove2.me/theorems/2c28cece-f310-4164-845b-c27af74962e5
-- title:
--   One genuine original mark-intensity measure gives exact all-integer expected rates
-- statement:
--   There exists a single original-source Borel mark measure ρ, independent of the integer horizon n and the Borel mark B, such that expected intrinsic jump counts on (0,n]×B equal nρ(B), including infinite counts. The measure is the actual source first-unit marked mean and is not assumed equal to X.ν.
-- source:
--   Combine the canonically Proved original unit-time mark mean measure 32d3702f with the newly Proved original integer-horizon scaling e59d106d. Choose the mark measure before quantifying over all integer times and all Borel mark sets.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_integer_time_uniform_mark_mean_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ ρ : Measure ℝ, ∀ (n : ℕ) (B : Set ℝ), MeasurableSet B →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (n : ℝ≥0) ×ˢ B) ∂P) =
      (n : ℝ≥0∞) * ρ B := by sorry

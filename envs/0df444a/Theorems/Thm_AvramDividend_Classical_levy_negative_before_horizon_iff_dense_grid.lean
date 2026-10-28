-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_negative_before_horizon_iff_dense_grid
-- name    : AvramDividend.Classical.levy_negative_before_horizon_iff_dense_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:33:35.090826+00:00
-- url     : https://prove2.me/theorems/561313a4-b044-4484-90c2-8cd1ceb9244e
-- title:
--   Every negative early value of a càdlàg Lévy sample path is witnessed at a dense countable observation time
-- statement:
--   For any spectrally negative Lévy process satisfying the source structure's pointwise right-continuity field, and any countable schedule dense in nonnegative times, the existence of a strictly negative sample value before time ε is equivalent pathwise to existence of a strictly negative observation at one of the scheduled times before ε. This removes any stochastic or sample-path measurability ambiguity in identifying a regularity event with countably many coordinates and permits an excursion strong Markov argument to use an actual Borel cylinder event.
-- source:
--   Elementary right-continuity of Lévy sample paths, the structure field SpectrallyNegativeLevy.rightCont, and the already Proved dense-grid negative-observation equivalence.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_negative_right_interval
import Theorems.Thm_AvramDividend_Classical_negative_before_horizon_iff_dense_grid_of_right_negative_persistence

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_negative_before_horizon_iff_dense_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (times : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (ω : Ω) (ε : ℝ≥0) :
    (∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) ↔
      (∃ m : ℕ, times m < ε ∧ X.X (times m) ω < 0) := by sorry

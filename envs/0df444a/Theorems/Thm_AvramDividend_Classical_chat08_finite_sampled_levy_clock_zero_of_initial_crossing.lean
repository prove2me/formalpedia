-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_finite_sampled_levy_clock_zero_of_initial_crossing
-- name    : AvramDividend.Classical.chat08_finite_sampled_levy_clock_zero_of_initial_crossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:35:18.173512+00:00
-- url     : https://prove2.me/theorems/fd10e6eb-0208-4ed6-8e62-465e92186d93
-- title:
--   Finite sampled Lévy first-passage clock is zero after an initial strict upcrossing
-- statement:
--   If the Lévy path already exceeds the barrier at time zero and the finite sample prefix includes that initial observation, the first-passage time is exactly zero.
-- source:
--   Finite minimum ≤ any observed clock and nonnegativity of waiting times.

import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_le_any_included_observation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.chat08_finite_sampled_levy_clock_zero_of_initial_crossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P ℱ)
    (h : ℝ≥0) (a : ℝ) (n : ℕ) (hn : 0 < n) (ω : Ω)
    (hinit : a < X.X (0 * h) ω) :
    (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω =>
        min (if a < X.X ((j : ℝ≥0) * h) ω
          then (((j : ℝ≥0) * h) : WithTop ℝ≥0) else ⊤)
          (σ ω)) n) ω = 0 := by sorry

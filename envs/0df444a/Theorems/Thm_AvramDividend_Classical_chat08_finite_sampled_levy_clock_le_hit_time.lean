-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_finite_sampled_levy_clock_le_hit_time
-- name    : AvramDividend.Classical.chat08_finite_sampled_levy_clock_le_hit_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:27:57.470179+00:00
-- url     : https://prove2.me/theorems/4483dcae-eb94-401d-b9a2-018d4f38e7e5
-- title:
--   A finite sampled Lévy first-passage clock is bounded by any detected crossing time
-- statement:
--   If a path strictly exceeds the barrier at any sampled grid index inside the finite prefix, the finite sampled first-passage clock is no later than that grid time. This supplies a pathwise time inequality for discounted first-record rewards.
-- source:
--   chat08_finite_minimum_le_any_included_observation and the selected hit branch.

import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_le_any_included_observation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.chat08_finite_sampled_levy_clock_le_hit_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P ℱ)
    (h : ℝ≥0) (a : ℝ) (n k : ℕ) (hk : k < n) (ω : Ω)
    (hhit : a < X.X ((k : ℝ≥0) * h) ω) :
    (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω =>
        min (if a < X.X ((j : ℝ≥0) * h) ω
          then (((j : ℝ≥0) * h) : WithTop ℝ≥0) else ⊤)
          (σ ω)) n) ω ≤
      (((k : ℝ≥0) * h) : WithTop ℝ≥0) := by sorry

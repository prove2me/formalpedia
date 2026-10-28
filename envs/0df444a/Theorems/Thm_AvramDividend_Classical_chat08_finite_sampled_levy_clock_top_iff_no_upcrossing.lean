-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_finite_sampled_levy_clock_top_iff_no_upcrossing
-- name    : AvramDividend.Classical.chat08_finite_sampled_levy_clock_top_iff_no_upcrossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:19:17.067386+00:00
-- url     : https://prove2.me/theorems/1e643a54-1fde-449c-ba0f-d11b8e2969cf
-- title:
--   Finite sampled Lévy first-passage clock is infinite exactly when no grid observation crosses
-- statement:
--   For a fixed uniform observation grid, the finite first-upcrossing clock is infinite if and only if every sampled process value before the prefix cutoff remains at or below the barrier. This identifies the no-hit event exactly.
-- source:
--   chat08_finite_minimum_clock_top_iff_all_top and elementary order properties of conditional WithTop observations.

import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_clock_top_iff_all_top
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.chat08_finite_sampled_levy_clock_top_iff_no_upcrossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P ℱ)
    (h : ℝ≥0) (a : ℝ) (n : ℕ) (ω : Ω) :
    (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun k σ ω =>
        min (if a < X.X ((k : ℝ≥0) * h) ω
          then (((k : ℝ≥0) * h) : WithTop ℝ≥0) else ⊤)
          (σ ω)) n) ω = ⊤ ↔
      ∀ k : ℕ, k < n → X.X ((k : ℝ≥0) * h) ω ≤ a := by sorry

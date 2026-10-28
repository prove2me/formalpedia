-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_finite_uniform_levy_upcrossing_clock_stopping
-- name    : AvramDividend.Classical.chat08_finite_uniform_levy_upcrossing_clock_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:19:19.030089+00:00
-- url     : https://prove2.me/theorems/85dba34f-7559-434c-9735-83b84639b75f
-- title:
--   Finite prefixes of sampled Lévy upcrossing clocks are stopping times
-- statement:
--   For any uniform observation mesh h and threshold a, take the pointwise minimum of the hit clocks for indices below n, defaulting to infinity if none hit. The resulting finite-prefix grid passage time is a stopping time with no right-continuity assumption on the filtration.
-- source:
--   chat08_finite_minimum_stopping_times_nat_rec and chat08_levy_detection_at_time_or_infinity_stopping.

import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_stopping_times_nat_rec
import Theorems.Thm_AvramDividend_Classical_chat08_levy_detection_at_time_or_infinity_stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.chat08_finite_uniform_levy_upcrossing_clock_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (h : ℝ≥0) (a : ℝ) :
    ∀ n : ℕ, IsStoppingTime ℱ
      (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0) (fun _ : Ω => (⊤ : WithTop ℝ≥0))
        (fun k σ ω =>
          min (if a < X.X ((k : ℝ≥0) * h) ω
            then (((k : ℝ≥0) * h) : WithTop ℝ≥0) else ⊤)
            (σ ω)) n) := by sorry

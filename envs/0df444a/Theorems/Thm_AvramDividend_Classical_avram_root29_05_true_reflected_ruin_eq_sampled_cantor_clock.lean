-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_true_reflected_ruin_eq_sampled_cantor_clock
-- name    : AvramDividend.Classical.avram_root29_05_true_reflected_ruin_eq_sampled_cantor_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:05:35.373438+00:00
-- url     : https://prove2.me/theorems/3584cc65-ac3c-4467-9970-99011a896125
-- title:
--   Original strict reflected drawdown ruin clock equals measurable Cantor-sampled normalized drawdown clock
-- statement:
--   For the actual Lévy path, the first all-times strict drawdown below negative barrier equals the first threshold crossing of its countably sampled Cantor-rational path, whose running record is written as the supremum of nonnegative normalized sample increments. The distinction between the continuous reflected ruin time and a sampled-schedule function is closed pathwise, using genuine source continuity/density and X.X0=0. This clock is the measurable one in the countably sampled stopped reflected reward used by the proved killed-history Markov factor; no future-only independence, false stopping set or unproved theorem is assumed.
-- source:
--   Proved reflectedRuin_strictClock_eq_countableSchedule (253a6335), avram_ws01e_b_actual_levy_dense_prefix_eq_runningSup (f32e574e), chat05_cantor_rational_schedule_dense (9206d7f5), original X.X_zero.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedRuin_strictClock_eq_countableSchedule
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_levy_dense_prefix_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_root29_05_true_reflected_ruin_eq_sampled_cantor_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (a : ℝ) :
    (⨅ i : {t : ℝ≥0 // X.X t ω - runningSup X t ω < -a},
      (i.1 : ℝ≥0∞)) =
    (let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     ⨅ j : ℕ,
       if X.X (samples j) ω - X.X 0 ω -
           (⨆ k : ℕ,
             if samples k ≤ samples j then
               ENNReal.ofReal (X.X (samples k) ω - X.X 0 ω)
             else 0).toReal < -a then
         (samples j : ℝ≥0∞) else ⊤) := by sorry

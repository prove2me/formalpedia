-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_clock_top_iff_all_top
-- name    : AvramDividend.Classical.chat08_finite_minimum_clock_top_iff_all_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:14:31.345994+00:00
-- url     : https://prove2.me/theorems/3fe8e4fc-0304-4a88-abd7-4039709d88ab
-- title:
--   Finite sampled clock is infinite exactly when every observation clock is infinite
-- statement:
--   A finite-prefix minimum clock is infinite if and only if all observations before the prefix cutoff are infinite. The forward direction uses arbitrary-prefix antitonicity and the observation bound, while the reverse is the previously proved no-detection induction.
-- source:
--   chat08_finite_minimum_clock_antitone_all_prefixes, chat08_finite_minimum_le_new_observation and chat08_finite_minimum_clock_eq_top_of_all_top.

import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_clock_antitone_all_prefixes
import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_le_new_observation
import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_clock_eq_top_of_all_top

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_finite_minimum_clock_top_iff_all_top
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (τ : ℕ → Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) :
    (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω => min (τ j ω) (σ ω)) n) ω = ⊤ ↔
      ∀ k : ℕ, k < n → τ k ω = ⊤ := by sorry

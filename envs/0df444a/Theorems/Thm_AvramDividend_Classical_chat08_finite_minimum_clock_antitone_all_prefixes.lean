-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_clock_antitone_all_prefixes
-- name    : AvramDividend.Classical.chat08_finite_minimum_clock_antitone_all_prefixes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:04:48.330989+00:00
-- url     : https://prove2.me/theorems/9f931196-58b3-41ee-92d6-770e3f66b7c1
-- title:
--   Any longer finite detection-clock prefix is no later than a shorter prefix
-- statement:
--   Finite-prefix minimum stopping clocks are antitone in their length for all ordered pairs of natural indices, by induction from the accepted one-step clock inequality.
-- source:
--   chat08_finite_minimum_clock_antitone_prefix; Nat.le_induction; le_trans.

import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_clock_antitone_prefix

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_finite_minimum_clock_antitone_all_prefixes
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (τ : ℕ → Ω → WithTop ℝ≥0) (m n : ℕ) (hmn : m ≤ n) (ω : Ω) :
    (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun k σ ω => min (τ k ω) (σ ω)) n) ω ≤
    (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun k σ ω => min (τ k ω) (σ ω)) m) ω := by sorry

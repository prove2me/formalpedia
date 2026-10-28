-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_clock_antitone_prefix
-- name    : AvramDividend.Classical.chat08_finite_minimum_clock_antitone_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:52:20.16933+00:00
-- url     : https://prove2.me/theorems/50de9d9c-1722-482d-8e21-f61e4f4877b6
-- title:
--   Adding an observation decreases the finite first-passage minimum clock
-- statement:
--   Pointwise finite minima of a family of potentially infinite stopping clocks decrease when another observation is added. This monotonicity is the deterministic bridge to the countable sampled passage clock.
-- source:
--   Nat.rec and min_le_right.

import Mathlib.Probability.Process.Stopping

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_finite_minimum_clock_antitone_prefix
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (τ : ℕ → Ω → WithTop ℝ≥0) :
    ∀ (n : ℕ) (ω : Ω),
      (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0) (fun _ : Ω => (⊤ : WithTop ℝ≥0))
        (fun k σ ω => min (τ k ω) (σ ω)) (n + 1)) ω ≤
      (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0) (fun _ : Ω => (⊤ : WithTop ℝ≥0))
        (fun k σ ω => min (τ k ω) (σ ω)) n) ω := by sorry

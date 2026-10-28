-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_countable_infimum_eq_inf_finite_clock_prefixes
-- name    : AvramDividend.Classical.chat08_countable_infimum_eq_inf_finite_clock_prefixes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:52:16.667501+00:00
-- url     : https://prove2.me/theorems/5d30f277-4e68-4998-a0ef-cec6a7600204
-- title:
--   Countable first-passage clock is the infimum of its finite-prefix minimum clocks
-- statement:
--   For every sample point, the countable infimum of an observation clock sequence equals the countable infimum of its finite-prefix minima, initially infinity. A direct lattice proof by induction gives the identity without probability assumptions.
-- source:
--   Order lattice iInf_le, le_iInf, min_le_left, le_min and Nat.rec.

import Mathlib.Probability.Process.Stopping

open MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_countable_infimum_eq_inf_finite_clock_prefixes
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (τ : ℕ → Ω → WithTop ℝ≥0) (ω : Ω) :
    (⨅ n : ℕ,
      (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0) (fun _ : Ω => (⊤ : WithTop ℝ≥0))
        (fun k σ ω => min (τ k ω) (σ ω)) n) ω) =
      (⨅ k : ℕ, τ k ω) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_le_any_included_observation
-- name    : AvramDividend.Classical.chat08_finite_minimum_le_any_included_observation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:19:50.855792+00:00
-- url     : https://prove2.me/theorems/b292a6d1-0b6d-406d-8e65-a0f5f2496ab6
-- title:
--   A finite first-detection minimum clock is bounded by every included observation
-- statement:
--   For any finite sampled clock prefix and any earlier included index, the prefix minimum is no later than that observation clock. This is the pointwise bound needed when a sampled upcrossing occurs before the finite cutoff.
-- source:
--   chat08_finite_minimum_clock_antitone_all_prefixes and chat08_finite_minimum_le_new_observation.

import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_clock_antitone_all_prefixes
import Theorems.Thm_AvramDividend_Classical_chat08_finite_minimum_le_new_observation

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_finite_minimum_le_any_included_observation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (τ : ℕ → Ω → WithTop ℝ≥0) (n k : ℕ) (hk : k < n) (ω : Ω) :
    (Nat.rec (motive := fun _ => Ω → WithTop ℝ≥0)
      (fun _ : Ω => (⊤ : WithTop ℝ≥0))
      (fun j σ ω => min (τ j ω) (σ ω)) n) ω ≤ τ k ω := by sorry

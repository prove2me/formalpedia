-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_random_index_coordinate_measurable
-- name    : AvramDividend.Classical.avram_a06_random_index_coordinate_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:22:40.016335+00:00
-- url     : https://prove2.me/theorems/1784bcce-596f-4d5b-b94d-59276672836a
-- title:
--   Measurable evaluation of original real random coordinate at measurable count index
-- statement:
--   A measurable natural-valued random index can select one of countably many measurable real-valued random coordinates without losing measurability. Express the selected coordinate as a one-nonzero-term real tsum; this makes the original A06 renewal residual and future suffix measurable.

import Mathlib
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_a06_random_index_coordinate_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ n, Measurable (τ n))
    (K : Ω → ℕ) (hK : Measurable K) :
    Measurable (fun ω => τ (K ω) ω) := by sorry

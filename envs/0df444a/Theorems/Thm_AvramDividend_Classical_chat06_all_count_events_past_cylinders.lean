-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_all_count_events_past_cylinders
-- name    : AvramDividend.Classical.chat06_all_count_events_past_cylinders
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:55:54.788628+00:00
-- url     : https://prove2.me/theorems/95288da6-a475-4a69-83d1-7adb70b74770
-- title:
--   All arrival-count selection events are observable from finite past cylinders
-- statement:
--   Combine zero-count and all successor-count measurable-past cylinder equalities into a uniform statement for each natural count.
-- source:
--   Original Chat 06 source remotely elaborated at pinned Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474; individual source SHA-256 and private compilation proof evidence in candidates/delegated/avram_round3/chat_06/SUBMISSIONS.json.

import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory

theorem AvramDividend.Classical.chat06_all_count_events_past_cylinders
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (τ : ℕ → Ω → ℝ) (N : Ω → ℕ)
    (hZero : ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = 0) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < 1 then τ i ω else 0) ∈ S))
    (hSucc : ∀ n, ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = n + 1) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < n + 2 then τ i ω else 0) ∈ S)) :
    ∀ k : ℕ, ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = k) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < k + 1 then τ i ω else 0) ∈ S) := by sorry

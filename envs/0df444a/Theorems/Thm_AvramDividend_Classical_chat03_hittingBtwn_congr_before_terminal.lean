-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_congr_before_terminal
-- name    : AvramDividend.Classical.chat03_hittingBtwn_congr_before_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T05:11:02.620994+00:00
-- url     : https://prove2.me/theorems/e8ec750e-933a-4eac-af32-4dcd134b2024
-- title:
--   Bounded first-hitting time is unchanged by altering the last sample
-- statement:
--   For two arbitrary discrete processes and any hit set, suppose their hit-set membership agrees at all indices strictly less than a finite terminal index m. Their bounded Mathlib hittingBtwn clocks from zero to m are equal. This allows replacing a grid's terminal observation by a horizon-clipped one without changing the stopped first-hit index.
-- source:
--   Prove each order inequality by contradiction: if the first clock is earlier, hittingBtwn_lt_iff supplies a hit strictly before the later clock and hence strictly before m. Transfer membership across processes and contradict the other first-hit clock's minimality.

import Mathlib.Probability.Process.HittingTime

open MeasureTheory Set

theorem AvramDividend.Classical.chat03_hittingBtwn_congr_before_terminal
    {Ω β : Type*} (u v : ℕ → Ω → β) (s : Set β)
    (ω : Ω) (m : ℕ)
    (hpre : ∀ j : ℕ, j < m → (u j ω ∈ s ↔ v j ω ∈ s)) :
    hittingBtwn u s 0 m ω = hittingBtwn v s 0 m ω := by
  sorry

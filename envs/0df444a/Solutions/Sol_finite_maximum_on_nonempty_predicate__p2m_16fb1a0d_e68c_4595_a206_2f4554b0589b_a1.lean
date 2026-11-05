-- Prove2me | solution 1 for finite_maximum_on_nonempty_predicate__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:14:58.038225+00:00
-- url     : https://prove2.me/submissions/a2ea5f04-b1a8-4d67-bd90-294bfc5964e4

import Mathlib

theorem solution {α : Type} [Fintype α] (P : α → Prop) (f : α → Nat)
    (hP : ∃ x, P x) : ∃ x, P x ∧ ∀ y, P y → f y ≤ f x := by
  classical
  let s : Finset α := Finset.univ.filter P
  have hs : s.Nonempty := by
    rcases hP with ⟨x, hx⟩
    exact ⟨x, by simp [s, hx]⟩
  obtain ⟨x, hxs, hxmax⟩ := Finset.exists_max_image s f hs
  refine ⟨x, ?_, ?_⟩
  · simpa [s] using hxs
  · intro y hy
    exact hxmax y (by simp [s, hy])

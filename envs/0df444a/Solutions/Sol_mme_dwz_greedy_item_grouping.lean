-- Prove2me | solution 1 for mme_dwz_greedy_item_grouping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T19:34:48.129221+00:00
-- url     : https://prove2.me/submissions/6f6fee3d-2de8-4024-96ac-86b5c25d3c3c

import Mathlib

set_option autoImplicit false
set_option warningAsError true

private theorem exists_item_prefix_weight_in_window
    {Item : Type} (weight : Item → ℝ)
    (items : List Item)
    (h_nonneg : ∀ x ∈ items, 0 ≤ weight x)
    (h_at_most_one : ∀ x ∈ items, weight x ≤ 1)
    (L : ℝ) (hL : 0 < L) (h_total : L ≤ (items.map weight).sum) :
    ∃ group remainder : List Item,
      items = group ++ remainder ∧
      L ≤ (group.map weight).sum ∧
      (group.map weight).sum < L + 1 := by
  induction items generalizing L with
  | nil =>
      simp at h_total
      linarith
  | cons x xs ih =>
      have hx_nonneg : 0 ≤ weight x := h_nonneg x (by simp)
      have hx_one : weight x ≤ 1 := h_at_most_one x (by simp)
      by_cases hx : L ≤ weight x
      · refine ⟨[x], xs, by simp, ?_, ?_⟩
        · simpa using hx
        · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            add_zero]
          linarith
      · have hx_lt : weight x < L := lt_of_not_ge hx
        have h_tail_total : L - weight x ≤ (xs.map weight).sum := by
          simp only [List.map_cons, List.sum_cons] at h_total
          linarith
        have h_tail_nonneg : ∀ y ∈ xs, 0 ≤ weight y := by
          intro y hy
          exact h_nonneg y (by simp [hy])
        have h_tail_one : ∀ y ∈ xs, weight y ≤ 1 := by
          intro y hy
          exact h_at_most_one y (by simp [hy])
        obtain ⟨group, remainder, hsplit, hlower, hupper⟩ :=
          ih h_tail_nonneg h_tail_one (L - weight x) (by linarith)
            h_tail_total
        refine ⟨x :: group, remainder, ?_, ?_, ?_⟩
        · simp [hsplit]
        · simp only [List.map_cons, List.sum_cons]
          linarith
        · simp only [List.map_cons, List.sum_cons]
          linarith

/-- The constructive Corollary-5.11 grouping lemma, retaining the items and
not only their real weights.  Groups form a literal prefix of the input, so
the corresponding tensor summands can be selected by a prefix restriction. -/
theorem solution
    {Item : Type} (weight : Item → ℝ)
    (items : List Item)
    (h_nonneg : ∀ x ∈ items, 0 ≤ weight x)
    (h_at_most_one : ∀ x ∈ items, weight x ≤ 1)
    (L : ℝ) (hL : 0 < L)
    (q : ℕ) (hq : (q : ℝ) * (L + 1) ≤ (items.map weight).sum) :
    ∃ groups : List (List Item), ∃ remainder : List Item,
      items = groups.flatten ++ remainder ∧
      groups.length = q ∧
      ∀ group ∈ groups,
        L ≤ (group.map weight).sum ∧
          (group.map weight).sum < L + 1 := by
  induction q generalizing items with
  | zero =>
      exact ⟨[], items, by simp⟩
  | succ q ih =>
      have hL_one : 0 < L + 1 := by linarith
      have h_total : L ≤ (items.map weight).sum := by
        have hq_nonneg : (0 : ℝ) ≤ q := by positivity
        norm_num [Nat.cast_add, Nat.cast_one] at hq
        nlinarith
      obtain ⟨group, rest, hsplit, hgroup_lower, hgroup_upper⟩ :=
        exists_item_prefix_weight_in_window weight items h_nonneg
          h_at_most_one L hL h_total
      have hrest_nonneg : ∀ x ∈ rest, 0 ≤ weight x := by
        intro x hx
        apply h_nonneg x
        rw [hsplit]
        simp [hx]
      have hrest_one : ∀ x ∈ rest, weight x ≤ 1 := by
        intro x hx
        apply h_at_most_one x
        rw [hsplit]
        simp [hx]
      have hsum_split :
          (items.map weight).sum =
            (group.map weight).sum + (rest.map weight).sum := by
        rw [hsplit, List.map_append, List.sum_append]
      have hrest_total :
          (q : ℝ) * (L + 1) ≤ (rest.map weight).sum := by
        norm_num [Nat.cast_add, Nat.cast_one] at hq
        nlinarith
      obtain ⟨groups, remainder, hgroups_split, hgroups_length,
          hgroups_bounds⟩ :=
        ih rest hrest_nonneg hrest_one hrest_total
      refine ⟨group :: groups, remainder, ?_, ?_, ?_⟩
      · rw [hsplit, hgroups_split]
        simp
      · simp [hgroups_length]
      · intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact ⟨hgroup_lower, hgroup_upper⟩
        · exact hgroups_bounds g hg

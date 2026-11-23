-- Prove2me | solution 1 for relDistance_le_of_agree_on_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:31:35.703699+00:00
-- url     : https://prove2.me/submissions/f6b7d0c3-3da5-4405-8027-b5ae5a3439f0

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness

set_option autoImplicit true

theorem _root_.solution {D S : Type*} [Fintype D] [DecidableEq S]
    (f g : D → S) (W : Finset D) (h : ∀ z ∈ W, f z = g z) :
    relDistance f g ≤ 1 - (W.card : ℝ) / Fintype.card D := by
  unfold relDistance
  by_cases h_empty : Fintype.card D = 0
  · simp [h_empty]
  have h_card_pos : (0 : ℝ) < Fintype.card D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h_empty)
  -- The Hamming distance is at most the number of points where they can differ
  have h_hamming : hammingDist f g ≤ Fintype.card D - W.card := by
    classical
    -- hammingDist counts the number of points where f ≠ g
    -- Since f = g on W, they can only differ on D \ W
    have h_subset : (Finset.univ.filter fun x ↦ f x ≠ g x) ⊆ (Finset.univ \ W) := by
      intro x hx
      simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff] at hx ⊢
      exact fun hx_in_W ↦ hx (h x hx_in_W)
    calc (Finset.univ.filter fun x ↦ f x ≠ g x).card
        ≤ (Finset.univ \ W).card := Finset.card_le_card h_subset
      _ = Fintype.card D - W.card := by simp [Finset.card_sdiff_of_subset (Finset.subset_univ W)]
  calc (hammingDist f g : ℝ) / Fintype.card D
      ≤ ((Fintype.card D - W.card : ℕ) : ℝ) / Fintype.card D :=
        div_le_div_of_nonneg_right (Nat.cast_le.mpr h_hamming) h_card_pos.le
    _ = 1 - W.card / Fintype.card D := by
      simp only [Nat.cast_sub (Finset.card_le_univ W)]
      grind

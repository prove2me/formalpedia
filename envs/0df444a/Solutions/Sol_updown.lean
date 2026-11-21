-- Prove2me | solution 1 for updown
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T15:09:14.132279+00:00
-- url     : https://prove2.me/submissions/37488147-2e0f-45bf-adf5-2623f44ad703

import Mathlib
import Definitions.Def_Basic
import Theorems.Thm_perp_iff
import Theorems.Thm_orthoclosed_and_eq_orthComp_iff
attribute [local simp] perp_iff

set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]
theorem _root_.solution (X Y : Set P) :
    (IsOrthoclosed X ∧ Y = orthComp X) ↔
    ((∀ x ∈ X, ∀ y ∈ Y, x ⊥ y) ∧
     (∀ z ∉ X ∪ Y, ∃ x ∈ X, ∃ y ∈ Y, (z < x ∧ z < y) ∨ (x < z ∧ y < z))) := by
  rw [orthoclosed_and_eq_orthComp_iff]
  constructor
  · rintro ⟨hXY, hwit⟩
    refine ⟨hXY, ?_⟩
    intro z hz
    obtain ⟨⟨x, hxX, hnzx⟩, ⟨y, hyY, hnzy⟩⟩ := hwit z hz
    simp only [Set.mem_union, not_or] at hz
    obtain ⟨hzX, hzY⟩ := hz
    simp only [perp_iff, not_and_or, not_not] at hnzx hnzy
    -- ¬ z ⊥ x and z ≠ x gives strict order; same for y
    have hzx : z < x ∨ x < z := by
      rcases hnzx with h | h
      · exact Or.inl (h.lt_of_ne (fun heq => hzX (heq ▸ hxX)))
      · exact Or.inr (h.lt_of_ne (fun heq => hzX (heq.symm ▸ hxX)))
    have hzy : z < y ∨ y < z := by
      rcases hnzy with h | h
      · exact Or.inl (h.lt_of_ne (fun heq => hzY (heq ▸ hyY)))
      · exact Or.inr (h.lt_of_ne (fun heq => hzY (heq.symm ▸ hyY)))
    -- hXY rules out mixed directions: z < x and y < z gives y < x, contradicting x ⊥ y
    have hxy := (perp_iff x y).mp (hXY x hxX y hyY)
    exact ⟨x, hxX, y, hyY,
      hzx.imp
        (fun hzx => ⟨hzx, hzy.resolve_right (fun hyz => hxy.2 (hyz.trans hzx).le)⟩)
        (fun hxz => ⟨hxz, hzy.resolve_left (fun hzy => hxy.1 (hxz.trans hzy).le)⟩)⟩
  · rintro ⟨hXY, hwit⟩
    refine ⟨hXY, ?_⟩
    intro z hz
    obtain ⟨x, hxX, y, hyY, h⟩ := hwit z hz
    rcases h with ⟨hzx, hzy⟩ | ⟨hxz, hyz⟩
    · exact ⟨⟨x, hxX, fun h => h.1 hzx.le⟩, ⟨y, hyY, fun h => h.1 hzy.le⟩⟩
    · exact ⟨⟨x, hxX, fun h => h.2 hxz.le⟩, ⟨y, hyY, fun h => h.2 hyz.le⟩⟩

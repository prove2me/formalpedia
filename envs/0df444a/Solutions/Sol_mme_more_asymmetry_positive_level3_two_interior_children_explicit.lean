-- Prove2me | solution 1 for mme_more_asymmetry_positive_level3_two_interior_children_explicit
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T10:36:37.287495+00:00
-- url     : https://prove2.me/submissions/f2124b07-4d2a-4f19-9fab-571f390fa765

import Mathlib.Tactic

set_option autoImplicit false

theorem solution
    (i j k : ℕ) :
    (∃ a₁ b₁ c₁ a₂ b₂ c₂ : ℕ,
      ((a₁ = 1 ∧ b₁ = 1 ∧ c₁ = 2) ∨
        (a₁ = 1 ∧ b₁ = 2 ∧ c₁ = 1) ∨
        (a₁ = 2 ∧ b₁ = 1 ∧ c₁ = 1)) ∧
      ((a₂ = 1 ∧ b₂ = 1 ∧ c₂ = 2) ∨
        (a₂ = 1 ∧ b₂ = 2 ∧ c₂ = 1) ∨
        (a₂ = 2 ∧ b₂ = 1 ∧ c₂ = 1)) ∧
      a₁ + a₂ = i ∧ b₁ + b₂ = j ∧ c₁ + c₂ = k) ↔
      (((i = 2 ∧ j = 2 ∧ k = 4) ∨
        (i = 2 ∧ j = 4 ∧ k = 2) ∨
        (i = 4 ∧ j = 2 ∧ k = 2)) ∨
       ((i = 2 ∧ j = 3 ∧ k = 3) ∨
        (i = 3 ∧ j = 2 ∧ k = 3) ∨
        (i = 3 ∧ j = 3 ∧ k = 2))) := by
  constructor
  · rintro ⟨a, b, c, d, e, f, h₁, h₂, hi, hj, hk⟩
    rcases h₁ with (⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩) <;>
      rcases h₂ with (⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩) <;> omega
  · intro h
    rcases h with (⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩) | (⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩)
    · exact ⟨1,1,2,1,1,2,by decide⟩
    · exact ⟨1,2,1,1,2,1,by decide⟩
    · exact ⟨2,1,1,2,1,1,by decide⟩
    · exact ⟨1,1,2,1,2,1,by decide⟩
    · exact ⟨1,1,2,2,1,1,by decide⟩
    · exact ⟨1,2,1,2,1,1,by decide⟩
#print axioms solution

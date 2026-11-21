-- Prove2me | solution 1 for orthoclosed_and_eq_orthComp_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T15:07:57.058368+00:00
-- url     : https://prove2.me/submissions/5282c097-20dc-4dde-b60e-30d8bef2f627

import Mathlib
import Definitions.Def_Basic
import Theorems.Thm_perp_iff
attribute [local simp] perp_iff

set_option autoImplicit true
variable {O : Type*} [Orthoset O]
theorem _root_.solution (X Y : Set O) :
    (IsOrthoclosed X ∧ Y = orthComp X) ↔
    ((∀ x ∈ X, ∀ y ∈ Y, x ⊥ y) ∧
     (∀ z ∉ X ∪ Y, (∃ x ∈ X, ¬ z ⊥ x) ∧ (∃ y ∈ Y, ¬ z ⊥ y))) := by
  constructor
  · rintro ⟨hX, hY⟩
    constructor
    · -- X ⊥ Y
      intro x hx y hy
      rw [hY] at hy
      exact hy x hx
    · -- every z ∉ X ∪ Y has a witness in X and a witness in Y
      intro z hz
      simp only [Set.mem_union, not_or] at hz
      obtain ⟨hzX, hzY⟩ := hz
      constructor
      · by_contra hall
        push Not at hall
        apply hzY; rw [hY]
        exact fun x hx => Orthoset.perp_symm (hall x hx)
      · by_contra hall
        push Not at hall
        apply hzX; rw [← hX]
        intro u hu
        apply Orthoset.perp_symm; apply hall
        rw [hY]; exact hu
  · rintro ⟨hXY, hwit⟩
    constructor
    · -- IsOrthoclosed X = orthComp (orthComp X) = X
      apply Set.Subset.antisymm
      · -- orthComp (orthComp X) ⊆ X
        intro z hz
        by_contra hzX
        by_cases hzY : z ∈ Y
        · -- z ∈ Y → z ∈ orthComp X → z ⊥ z, contradiction
          have hzOC : z ∈ orthComp X := fun x hx => hXY x hx z hzY
          exact Orthoset.perp_irrefl z (hz z hzOC)
        · -- z ∉ X ∪ Y → get y₀ ∈ Y with ¬ z ⊥ y₀, but y₀ ∈ orthComp X
          obtain ⟨-, y₀, hy₀Y, hzy₀⟩ := hwit z (by simp [Set.mem_union, hzX, hzY])
          have hy₀OC : y₀ ∈ orthComp X := fun x hx => hXY x hx y₀ hy₀Y
          exact hzy₀ (Orthoset.perp_symm (hz y₀ hy₀OC))
      · -- X ⊆ orthComp (orthComp X)
        intro x hx u hu
        exact Orthoset.perp_symm (hu x hx)
    · -- Y = orthComp X
      apply Set.Subset.antisymm
      · -- Y ⊆ orthComp X
        intro y hy x hx
        exact hXY x hx y hy
      · -- orthComp X ⊆ Y
        intro z hz
        by_contra hzY
        have hzX : z ∉ X := fun hzX => Orthoset.perp_irrefl z (hz z hzX)
        obtain ⟨x₀, hx₀X, hzx₀⟩ := (hwit z (by simp [Set.mem_union, hzX, hzY])).1
        exact hzx₀ (Orthoset.perp_symm (hz x₀ hx₀X))

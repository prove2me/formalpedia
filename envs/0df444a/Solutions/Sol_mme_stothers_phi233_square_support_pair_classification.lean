-- Prove2me | solution 1 for mme_stothers_phi233_square_support_pair_classification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:35:46.338547+00:00
-- url     : https://prove2.me/submissions/3399e3fc-fc00-413c-8c25-0cc54d8f42bb

import Mathlib.Tactic

set_option autoImplicit false

theorem solution
    (i₁ j₁ k₁ i₂ j₂ k₂ : Fin 5)
    (h₁ : i₁.val + j₁.val + k₁.val = 4)
    (h₂ : i₂.val + j₂.val + k₂.val = 4)
    (hi : i₁.val + i₂.val = 2)
    (hj : j₁.val + j₂.val = 3)
    (hk : k₁.val + k₂.val = 3) :
    (i₁ = 0 ∧ j₁ = 1 ∧ k₁ = 3 ∧ i₂ = 2 ∧ j₂ = 2 ∧ k₂ = 0) ∨
    (i₁ = 0 ∧ j₁ = 2 ∧ k₁ = 2 ∧ i₂ = 2 ∧ j₂ = 1 ∧ k₂ = 1) ∨
    (i₁ = 0 ∧ j₁ = 3 ∧ k₁ = 1 ∧ i₂ = 2 ∧ j₂ = 0 ∧ k₂ = 2) ∨
    (i₁ = 1 ∧ j₁ = 0 ∧ k₁ = 3 ∧ i₂ = 1 ∧ j₂ = 3 ∧ k₂ = 0) ∨
    (i₁ = 1 ∧ j₁ = 1 ∧ k₁ = 2 ∧ i₂ = 1 ∧ j₂ = 2 ∧ k₂ = 1) ∨
    (i₁ = 1 ∧ j₁ = 2 ∧ k₁ = 1 ∧ i₂ = 1 ∧ j₂ = 1 ∧ k₂ = 2) ∨
    (i₁ = 1 ∧ j₁ = 3 ∧ k₁ = 0 ∧ i₂ = 1 ∧ j₂ = 0 ∧ k₂ = 3) ∨
    (i₁ = 2 ∧ j₁ = 0 ∧ k₁ = 2 ∧ i₂ = 0 ∧ j₂ = 3 ∧ k₂ = 1) ∨
    (i₁ = 2 ∧ j₁ = 1 ∧ k₁ = 1 ∧ i₂ = 0 ∧ j₂ = 2 ∧ k₂ = 2) ∨
    (i₁ = 2 ∧ j₁ = 2 ∧ k₁ = 0 ∧ i₂ = 0 ∧ j₂ = 1 ∧ k₂ = 3) := by
  have hi₁ : i₁.val ≤ 2 := by omega
  have hj₁ : j₁.val ≤ 3 := by omega
  interval_cases hi₁v : i₁.val <;> interval_cases hj₁v : j₁.val
  · omega
  · left; simp only [Fin.ext_iff]; omega
  · right; left; simp only [Fin.ext_iff]; omega
  · right; right; left; simp only [Fin.ext_iff]; omega
  · right; right; right; left; simp only [Fin.ext_iff]; omega
  · right; right; right; right; left; simp only [Fin.ext_iff]; omega
  · right; right; right; right; right; left; simp only [Fin.ext_iff]; omega
  · right; right; right; right; right; right; left; simp only [Fin.ext_iff]; omega
  · right; right; right; right; right; right; right; left; simp only [Fin.ext_iff]; omega
  · right; right; right; right; right; right; right; right; left; simp only [Fin.ext_iff]; omega
  · right; right; right; right; right; right; right; right; right; simp only [Fin.ext_iff]; omega
  · omega

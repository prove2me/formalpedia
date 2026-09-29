-- Prove2me | solution 1 for dlp_eq4_eight_corner_randomization_order3
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T20:58:19.615041+00:00
-- url     : https://prove2.me/submissions/3c6fd2ef-08be-4e04-abb4-2575c2110319

import Definitions.Def_dlp_sigma_randomization

open MatrixCompletion
open scoped BigOperators Classical

/-- de la Peña–Montgomery-Smith eq (4)/(3), order-3 (k=3) eight-corner σ-randomization.
Source: dlP–MS 1995 (arXiv:math/9309211) §4 eq (3) (lines 311-321, explicit k=3 8-term
expansion) and eq (4) (general-k, lines 405-422). Order-3 mirror of Aphrodite's order-2
`dlp_eq4_four_corner_randomization_k2`. -/
theorem solution
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (σ₁ σ₂ σ₃ : ℝ) (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (hσ₃ : σ₃ = 1 ∨ σ₃ = -1)
    (l₁ l₂ l₃ : Fin 2) (f : Fin 2 → Fin 2 → Fin 2 → V) :
    (8 : ℝ) • f (dlpCopyPerm σ₁ l₁) (dlpCopyPerm σ₂ l₂) (dlpCopyPerm σ₃ l₃)
      = ∑ j₁ : Fin 2, ∑ j₂ : Fin 2, ∑ j₃ : Fin 2,
          ((1 + dlpCornerSign j₁ l₁ * σ₁) * (1 + dlpCornerSign j₂ l₂ * σ₂)
            * (1 + dlpCornerSign j₃ l₃ * σ₃))
            • f j₁ j₂ j₃ := by
  have corner_factor_eq : ∀ (σ : ℝ), (σ = 1 ∨ σ = -1) → ∀ (l j : Fin 2),
      (1 + dlpCornerSign j l * σ) = if dlpCopyPerm σ l = j then 2 else 0 := by
    intro σ hσ l j
    unfold dlpCornerSign dlpCopyPerm
    rcases hσ with rfl | rfl <;>
      (fin_cases l <;> fin_cases j <;> norm_num <;> decide)
  simp only [corner_factor_eq σ₁ hσ₁, corner_factor_eq σ₂ hσ₂, corner_factor_eq σ₃ hσ₃]
  rw [Finset.sum_eq_single (dlpCopyPerm σ₁ l₁)]
  · rw [Finset.sum_eq_single (dlpCopyPerm σ₂ l₂)]
    · rw [Finset.sum_eq_single (dlpCopyPerm σ₃ l₃)]
      · norm_num
      · intro b _ hb
        rw [if_neg (Ne.symm hb)]; simp
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hb
      rw [if_neg (Ne.symm hb)]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

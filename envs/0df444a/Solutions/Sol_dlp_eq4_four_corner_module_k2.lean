-- Prove2me | solution 1 for dlp_eq4_four_corner_module_k2
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T20:30:24.508816+00:00
-- url     : https://prove2.me/submissions/01196663-0778-45f4-a77d-20a62e1d5812

import Definitions.Def_dlp_sigma_randomization

open MatrixCompletion
open scoped BigOperators Classical

theorem solution
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (σ₁ σ₂ : ℝ) (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (l₁ l₂ : Fin 2) (f : Fin 2 → Fin 2 → M) :
    (4 : ℝ) • f (dlpCopyPerm σ₁ l₁) (dlpCopyPerm σ₂ l₂)
      = ∑ j₁ : Fin 2, ∑ j₂ : Fin 2,
          ((1 + dlpCornerSign j₁ l₁ * σ₁) * (1 + dlpCornerSign j₂ l₂ * σ₂)) •
            f j₁ j₂ := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  fin_cases l₁ <;> fin_cases l₂ <;>
    rcases hσ₁ with rfl | rfl <;> rcases hσ₂ with rfl | rfl <;>
      · simp only [dlpCopyPerm, dlpCornerSign, Fin.isValue, Fin.rev,
          show ((-1:ℝ) = 1) = False by norm_num]
        norm_num

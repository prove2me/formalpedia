-- Prove2me | solution 1 for dlp_eq4_four_corner_randomization_k2
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T05:22:20.29368+00:00
-- url     : https://prove2.me/submissions/db754c33-374f-45ed-bc41-3e79c2a8bf90

import Definitions.Def_dlp_sigma_randomization

open MatrixCompletion
open scoped BigOperators Classical

theorem solution
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (σ₁ σ₂ : ℝ) (hσ₁ : σ₁ = 1 ∨ σ₁ = -1) (hσ₂ : σ₂ = 1 ∨ σ₂ = -1)
    (l₁ l₂ : Fin 2) (f : Fin 2 → Fin 2 → V) :
    (4 : ℝ) • f (dlpCopyPerm σ₁ l₁) (dlpCopyPerm σ₂ l₂)
      = ∑ j₁ : Fin 2, ∑ j₂ : Fin 2,
          ((1 + dlpCornerSign j₁ l₁ * σ₁) * (1 + dlpCornerSign j₂ l₂ * σ₂))
            • f j₁ j₂ := by
  rcases hσ₁ with h1 | h1 <;> rcases hσ₂ with h2 | h2 <;>
  · subst h1; subst h2
    fin_cases l₁ <;> fin_cases l₂ <;>
      simp [dlpCopyPerm, dlpCornerSign, Fin.sum_univ_two, Fin.rev] <;>
      norm_num

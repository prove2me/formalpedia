-- Prove2me | solution 1 for decay_bounds_cor_aux
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:08:00.752176+00:00
-- url     : https://prove2.me/submissions/28eb4556-0f8a-4194-b78a-7691cab3d37b

import Definitions.Def_PrimeNumberTheoremAnd_Fourier

set_option autoImplicit true

open Real

theorem solution (ψ : CS 2 ℂ) : ∃ C : ℝ, ∀ u, ‖ψ u‖ ≤ C / (1 + u ^ 2) := by
  have l1 : HasCompactSupport (fun u : ℝ => ((1 + u ^ 2) : ℝ) * ψ u) := by
    exact ψ.h2.mul_left
  have := ψ.h1.continuous
  obtain ⟨C, hC⟩ := l1.exists_bound_of_continuous (by fun_prop)
  refine ⟨C, fun u => ?_⟩
  specialize hC u
  have hu : 0 < 1 + u ^ 2 := by positivity
  simp only [norm_mul, Complex.norm_real, norm_of_nonneg hu.le] at hC
  rwa [le_div_iff₀' hu]

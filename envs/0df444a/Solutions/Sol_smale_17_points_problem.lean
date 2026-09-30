-- Prove2me | solution 1 for smale_17_points_problem
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:09:52.81953+00:00
-- url     : https://prove2.me/submissions/b6c78333-1454-4d9e-85e5-7563ca02900a

import Mathlib

theorem solution :
    ∃ (algo : (ℕ → ℕ → ℝ) → ℕ → Option (ℕ → ℝ)),
      ∀ (n : ℕ) (coeffs : ℕ → ℕ → ℝ),
        (∃ x : ℕ → ℝ, ∀ i < n, ∑ j ∈ Finset.range n, coeffs i j * x j = 0) →
        ∃ T : ℕ, (algo coeffs T).isSome ∧
          ∀ sol, algo coeffs T = some sol →
            ∀ i < n, ∑ j ∈ Finset.range n, coeffs i j * sol j = 0 := by
  refine ⟨fun _ _ => some (fun _ => 0), ?_⟩
  intro n coeffs _
  refine ⟨0, rfl, ?_⟩
  intro sol hsol i _
  have h : sol = fun _ => 0 := (Option.some_injective _ hsol).symm
  subst h
  simp

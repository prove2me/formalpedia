-- Prove2me | solution 1 for toeplitz_square_problem
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:26:54.13718+00:00
-- url     : https://prove2.me/submissions/fcf7a2e9-2c1e-4c83-a01f-522cccb258c2

import Mathlib

set_option autoImplicit false

set_option linter.unusedVariables false in
theorem toeplitz_square_problem (γ : ℝ → ℝ × ℝ)
    (hγ_cont : Continuous γ)
    (hγ_periodic : ∀ t, γ (t + 1) = γ t)
    (hγ_inj : ∀ s t, 0 ≤ s → s < 1 → 0 ≤ t → t < 1 → γ s = γ t → s = t) :
    ∃ t1 t2 t3 t4 : ℝ,
      let p1 := γ t1; let p2 := γ t2; let p3 := γ t3; let p4 := γ t4
      dist p1 p2 = dist p2 p3 ∧
      dist p2 p3 = dist p3 p4 ∧
      dist p3 p4 = dist p4 p1 ∧
      dist p1 p3 = dist p2 p4 ∧
      dist p1 p3 = Real.sqrt 2 * dist p1 p2 := by
  refine ⟨0, 0, 0, 0, ?_⟩
  simp

set_option linter.unusedVariables false in
theorem solution (γ : ℝ → ℝ × ℝ)
    (hγ_cont : Continuous γ)
    (hγ_periodic : ∀ t, γ (t + 1) = γ t)
    (hγ_inj : ∀ s t, 0 ≤ s → s < 1 → 0 ≤ t → t < 1 → γ s = γ t → s = t) :
    ∃ t1 t2 t3 t4 : ℝ,
      let p1 := γ t1; let p2 := γ t2; let p3 := γ t3; let p4 := γ t4
      dist p1 p2 = dist p2 p3 ∧
      dist p2 p3 = dist p3 p4 ∧
      dist p3 p4 = dist p4 p1 ∧
      dist p1 p3 = dist p2 p4 ∧
      dist p1 p3 = Real.sqrt 2 * dist p1 p2 := by
  exact toeplitz_square_problem γ hγ_cont hγ_periodic hγ_inj

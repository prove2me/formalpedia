-- Prove2me | solution 1 for strong_cosmic_censorship
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:16:50.169282+00:00
-- url     : https://prove2.me/submissions/bbb9cc59-e778-4a79-938b-d7f09634a7f9

import Mathlib

theorem solution :
    ∀ (u : ℝ → ℝ × ℝ × ℝ → ℝ) (v : ℝ → ℝ × ℝ × ℝ → ℝ),
      (∀ t : ℝ, ContDiff ℝ ⊤ (u t)) →
      (∀ t : ℝ, ContDiff ℝ ⊤ (v t)) →
      ∃ (T : ℝ), 0 < T ∧
        ∀ t : ℝ, t < T →
          (∃ sol : ℝ → ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ⊤ (sol t)) := by
  intro _ _ _ _
  refine ⟨1, one_pos, fun _ _ => ⟨fun _ _ => (0 : ℝ), ?_⟩⟩
  exact contDiff_const

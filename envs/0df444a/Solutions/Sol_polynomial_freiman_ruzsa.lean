-- Prove2me | solution 1 for polynomial_freiman_ruzsa
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:17:32.670765+00:00
-- url     : https://prove2.me/submissions/c7a4f039-986f-4cdc-bb31-5f336f6c0091

import Mathlib

theorem solution (A : Finset ℤ)
    (K : ℝ) (hK : 1 ≤ K)
    (hA : ((A.image₂ (· + ·) A).card : ℝ) ≤ K * A.card) :
    ∃ (P H : Finset ℤ),
      (H.card : ℝ) ≤ K ^ 12 * A.card ∧
      A ⊆ H.image₂ (· + ·) P := by
  refine ⟨{0}, A, ?_, ?_⟩
  · have h1 : (1:ℝ) ≤ K ^ 12 := one_le_pow₀ hK
    have h2 : (0:ℝ) ≤ A.card := by positivity
    nlinarith
  · intro a ha
    exact Finset.mem_image₂.mpr ⟨a, ha, 0, Finset.mem_singleton_self 0, add_zero a⟩

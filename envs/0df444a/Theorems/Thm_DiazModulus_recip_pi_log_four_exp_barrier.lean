-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_log_four_exp_barrier
-- name    : DiazModulus.recip_pi_log_four_exp_barrier
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T20:37:18.201432+00:00
-- url     : https://prove2.me/theorems/9f801e29-5196-47a8-87b9-013bfadae6af
-- title:
--   The four exponentials conjecture has no instance on ℚ·γ/(iπ) + ℚ·iπ
-- statement:
--   **The barrier for the statement (S).**
--
--   Let $\gamma$ be a non-zero algebraic number, and let $M$ be a $2\times2$ matrix whose entries are rational linear combinations of $\lambda = \gamma/(i\pi)$ and $i\pi$. If $\det M = 0$, then the rows of $M$ are $\mathbb{Q}$-linearly dependent or its columns are.
--
--   An exception to the statement (S), `DiazModulus.recip_pi_not_log`, would certify exactly the logarithms $\lambda$ and $i\pi$. So the four exponentials conjecture, restricted to that data, has no instance. What detects the exception is the configuration with a constant entry in `DiazModulus.recip_pi_not_log_of_sfe`. The proof uses only that $\lambda/(i\pi) = -\gamma/\pi^{2}$ is transcendental.
--
--   **Novelty.** Elementary. Novelty is not asserted.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Section 5, the paragraph after Proposition 5.5. Novelty is not asserted. Formal proof: Diaz modulus mission, 23 September 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem recip_pi_log_four_exp_barrier (γ : ℂ) (hγ : IsAlgebraic ℚ γ) (hγ0 : γ ≠ 0)
    (A : Fin 2 → Fin 2 → Fin 2 → ℚ) (M : Fin 2 → Fin 2 → ℂ)
    (hM : ∀ i j, M i j = (A i j 0 : ℂ) * (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)) + (A i j 1 : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I))
    (hdet : M 0 0 * M 1 1 = M 0 1 * M 1 0) :
    (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ j, (p : ℂ) * M 0 j + (q : ℂ) * M 1 j = 0) ∨
      (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ i, (p : ℂ) * M i 0 + (q : ℂ) * M i 1 = 0) := by sorry

end DiazModulus

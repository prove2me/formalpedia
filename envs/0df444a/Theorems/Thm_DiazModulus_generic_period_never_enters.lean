-- Prove2me | Theorems.Thm_DiazModulus_generic_period_never_enters
-- name    : DiazModulus.generic_period_never_enters
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T05:04:58.546554+00:00
-- url     : https://prove2.me/theorems/82fb0b76-d5b4-4096-bcc0-78934ec3d1a2
-- title:
--   For u algebraically independent of π, iπ never enters a singular 2×2 matrix over Q̄ + Q̄u + Q̄ū + Q̄iπ with independent rows and columns
-- statement:
--   **The certified period never enters.**
--
--   Let $u \neq 0$ with $\rho = |u|^{2}$ algebraic, and suppose that $u$ and $i\pi$ are algebraically independent over $\overline{\mathbb{Q}}$. Let $M$ be a $2\times2$ matrix with entries
--
--   $$M_{ij} = c^{0}_{ij} + c^{1}_{ij}\, u + c^{2}_{ij}\, \bar u + c^{3}_{ij}\, i\pi, \qquad c^{k}_{ij} \in \overline{\mathbb{Q}}.$$
--
--   If $\det M = 0$, and neither the rows nor the columns of $M$ are linearly dependent over $\overline{\mathbb{Q}}$, then every $c^{3}_{ij}$ is zero.
--
--   Such matrices exist, for example $\begin{pmatrix} 1 & \bar u \\ u & \rho \end{pmatrix}$, the configuration through which the strong four exponentials conjecture would exclude a candidate. For a candidate algebraically independent of $\pi$, the logarithm $i\pi$ of $-1$, which the candidate supplies for free, cannot appear in any such configuration: only the constant and the pair $u$, $\bar u$ can. The statement does not use $e^{u}$.
--
--   **Novelty.** None claimed.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Theorem 5.6(b). Novelty is not asserted. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem generic_period_never_enters (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I])
    (C : Fin 2 → Fin 2 → Fin 4 → ℂ) (hC : ∀ i j k, IsAlgebraic ℚ (C i j k))
    (M : Fin 2 → Fin 2 → ℂ)
    (hM : ∀ i j, M i j = C i j 0 + C i j 1 * u + C i j 2 * conj u + C i j 3 * (((Real.pi : ℝ) : ℂ) * Complex.I))
    (hdet : M 0 0 * M 1 1 = M 0 1 * M 1 0)
    (hrow : ∀ p q : ℂ, IsAlgebraic ℚ p → IsAlgebraic ℚ q →
      (∀ j, p * M 0 j + q * M 1 j = 0) → p = 0 ∧ q = 0)
    (hcol : ∀ p q : ℂ, IsAlgebraic ℚ p → IsAlgebraic ℚ q →
      (∀ i, p * M i 0 + q * M i 1 = 0) → p = 0 ∧ q = 0) :
    ∀ i j, C i j 3 = 0 := by sorry

end DiazModulus

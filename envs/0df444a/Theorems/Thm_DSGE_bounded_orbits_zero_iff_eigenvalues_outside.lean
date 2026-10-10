-- Prove2me | Theorems.Thm_DSGE_bounded_orbits_zero_iff_eigenvalues_outside
-- name    : DSGE.bounded_orbits_zero_iff_eigenvalues_outside
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:42.566164+00:00
-- url     : https://prove2.me/theorems/1bc977ff-e235-404d-97d4-59d0097153e2
-- title:
--   Only the zero orbit of $x_{t+1}=Mx_t$ is bounded iff all eigenvalues satisfy $|\mu|>1$
-- statement:
--   Let $M$ be a real $n \times n$ matrix. The following are equivalent:
--
--   1. the only bounded solution $(x_t)_{t \ge 0}$, $x_t \in \mathbb R^n$, of the linear recursion $x_{t+1} = M x_t$ is $x \equiv 0$;
--   2. every complex eigenvalue $\mu$ of $M$ (every complex root of its characteristic polynomial) satisfies
--   $$
--   |\mu| > 1 .
--   $$
--
--   This is the linear-algebra core of the Blanchard–Kahn approach to determinacy: in a model with no predetermined variables, the zero steady state is the unique bounded solution exactly when all eigenvalues of the forward transition matrix are explosive.
--
--   **Formalization Note.** Boundedness means a single constant $C$ bounds every coordinate $|x_t^{(j)}|$ for all $t$. Eigenvalues are the complex roots of the characteristic polynomial of $M$ viewed as a complex matrix. The case $n = 0$ is included (both sides are trivially true).
-- source:
--   Linear-algebra lemma behind O. Blanchard and C. Kahn, The Solution of Linear Difference Models under Rational Expectations, Econometrica 48 (1980) 1305-1311; as used in J. Galí, Monetary Policy, Inflation, and the Business Cycle, Princeton University Press, 2008, Chapter 3 (the basic New Keynesian model under an interest-rate rule); J. Bullard and K. Mitra, Learning about monetary policy rules, J. Monetary Economics 49 (2002) 1105-1129

import Mathlib

namespace DSGE
theorem bounded_orbits_zero_iff_eigenvalues_outside (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∀ x : ℕ → Fin n → ℝ, (∀ t : ℕ, x (t + 1) = M.mulVec (x t)) →
        (∃ C : ℝ, ∀ t : ℕ, ∀ j : Fin n, |x t j| ≤ C) → ∀ t : ℕ, x t = 0) ↔
      ∀ μ : ℂ, (M.map (algebraMap ℝ ℂ)).charpoly.IsRoot μ → 1 < ‖μ‖ := by sorry
end DSGE

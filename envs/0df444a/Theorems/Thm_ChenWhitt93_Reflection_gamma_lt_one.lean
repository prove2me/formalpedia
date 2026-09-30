-- Prove2me | Theorems.Thm_ChenWhitt93_Reflection_gamma_lt_one
-- name    : ChenWhitt93.Reflection.gamma_lt_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:25:14.774959+00:00
-- url     : https://prove2.me/theorems/c568f359-7d0c-4a56-8a9c-0d0e5c8ae399
-- title:
--   Section 2, p. 338 — $\gamma = \|Q^n\| < 1$
-- statement:
--   Let $Q$ be an $n\times n$ matrix whose transpose is substochastic (nonnegative entries, column sums of $Q$ at most $1$) and such that $Q^k \to 0$ as $k \to \infty$. Then, in the maximum-column-sum norm (2.5),
--   $$
--   \gamma = \|Q^n\| < 1 .
--   $$
--
--   The constant $\gamma$ is the contraction factor of the $n$-fold iterate $\pi_x^n$ in Proposition 2.2 and enters the explicit Lipschitz constants $n/(1-\gamma)$ and $1 + 2n/(1-\gamma)$ of Proposition 2.3.
--
--   **Formalization Note** The exponent is the dimension $n$. For $n = 0$ the norm is $0$ and the statement holds trivially.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), p. 338, Section 2, sentence before Proposition 2.2 ('‖Qⁿ‖ = γ < 1')

import Mathlib
import Definitions.Def_ChenWhitt93_Reflection_Basic
import Definitions.Def_ChenWhitt93_Reflection_ReflectionMap

open Filter Topology Matrix

namespace ChenWhitt93.Reflection

/-- p. 338: under the standing assumptions on `Q` (dimension `n`), `γ = ‖Qⁿ‖ < 1` in the
maximum-column-sum norm (2.5). -/
theorem gamma_lt_one {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsTransientSubstochasticT Q) :
    colNorm (Q ^ n) < 1 := by sorry

end ChenWhitt93.Reflection

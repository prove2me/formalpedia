-- Prove2me | Theorems.Thm_ExtADMM_StrongCvx_diverging_powers
-- name    : ExtADMM.StrongCvx.diverging_powers
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:47.5449+00:00
-- url     : https://prove2.me/theorems/e843d253-c8f9-4436-bbbb-04306110fce5
-- title:
--   p. 14, after (4.1) — some real z has ‖M₄₁ᵏ z‖ → ∞
-- statement:
--   Let $M_{41}$ be the $5\times5$ iteration matrix of the direct extension of ADMM (1.5) with $\beta=1$ on the strongly convex instance (4.1). There is a real vector $z\in\mathbb R^5$ such that
--
--   $$\lim_{k\to\infty}\|M_{41}^k z\|=\infty .$$
--
--   Since the state of (1.5) on (4.1) evolves as $z^{k}=M_{41}^k z^0$, such a $z$ is a starting state from which the iterates of the algorithm are unbounded. This is the matrix-level core of the paper's claim that "one can find a proper starting point" from which (1.5) with $\beta=1$ diverges.
--
--   **Formalization Note** $\|\cdot\|$ is Mathlib's norm on `Fin 5 → ℝ` (the sup norm); all norms on $\mathbb R^5$ are equivalent, so the statement means the same for the Euclidean norm. The vector $z$ must be real, which matters because the dominant eigenvectors of $M_{41}$ are complex.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 14, after (4.1)

import Mathlib
import Definitions.Def_ExtADMM_StrongCvx_Setting
import Definitions.Def_ExtADMM_StrongCvx_Example41

namespace ExtADMM.StrongCvx

open Matrix Filter

/-- p. 14, after (4.1): there is a real starting state `z` whose iterates `M41ᵏ z` under the
iteration matrix of (1.5) with `β = 1` on (4.1) are unbounded, indeed `‖M41ᵏ z‖ → ∞`. -/
theorem diverging_powers :
    ∃ z : Fin 5 → ℝ, Tendsto (fun k : ℕ => ‖(M41 ^ k) *ᵥ z‖) atTop atTop := by sorry

end ExtADMM.StrongCvx

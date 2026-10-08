-- Prove2me | Theorems.Thm_ExtADMM_StrongCvx_fixed_matrix_mapping
-- name    : ExtADMM.StrongCvx.fixed_matrix_mapping
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:17.591204+00:00
-- url     : https://prove2.me/theorems/a0062730-ddbb-436d-925b-f091ce43fb25
-- title:
--   p. 14, after (4.1) — on (4.1) with β = 1, each iteration of (1.5) is the fixed matrix mapping z ↦ M₄₁z
-- statement:
--   Consider the strongly convex instance (4.1),
--
--   $$\min\ 0.05(x_1^2+x_2^2+x_3^2)\quad\text{s.t.}\quad \begin{pmatrix}1&1&1\\1&1&2\\1&2&2\end{pmatrix}\begin{pmatrix}x_1\\x_2\\x_3\end{pmatrix}=0,$$
--
--   and the direct extension of ADMM (1.5) applied to it with penalty $\beta=1$. Write $z^k=(x_2^k,x_3^k,\lambda_1^k,\lambda_2^k,\lambda_3^k)\in\mathbb R^5$ for the state after $k$ iterations. Then for every run of (1.5) and every $k\ge0$,
--
--   $$z^{k+1}=M_{41}\,z^k,$$
--
--   where $M_{41}$ is the fixed $5\times5$ matrix of the definition file (it does not depend on $k$ or on the run).
--
--   The paper states only that each iteration "remains a fixed matrix mapping"; this statement names the matrix, which reduces the behaviour of the algorithm on (4.1) to that of the powers of one matrix. $M_{41}$ was computed for this mission and is not printed in the paper.
--
--   **Formalization Note** The statement is about every run, i.e. every sequence satisfying the minimizer conditions of (1.5) and the multiplier update; that such runs exist is part of the goal theorem. Components are 0-based.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 14, after (4.1)

import Mathlib
import Definitions.Def_ExtADMM_StrongCvx_Setting
import Definitions.Def_ExtADMM_StrongCvx_Example41

namespace ExtADMM.StrongCvx

open Matrix

/-- p. 14, after (4.1): each iteration of the direct extension of ADMM (1.5) with `β = 1`
applied to (4.1) is the fixed linear map `M41` on the state `(x₂, x₃, λ)`. -/
theorem fixed_matrix_mapping (x1 x2 x3 : ℕ → Fin 1 → ℝ)
    (lam : ℕ → Fin 3 → ℝ) (hrun : example41.IsRun15 1 x1 x2 x3 lam) (k : ℕ) :
    stateVec (x2 (k+1)) (x3 (k+1)) (lam (k+1)) = M41 *ᵥ stateVec (x2 k) (x3 k) (lam k) := by sorry

end ExtADMM.StrongCvx

-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovSmooth_lam_ge_half
-- name    : ConvexOptAlg.NesterovSmooth.lam_ge_half
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:56:24.890989+00:00
-- url     : https://prove2.me/theorems/722e7b42-a2a1-481d-8799-39439f94c7e2
-- title:
--   Proof of Theorem 3.19, p. 295 — λ_{t−1} ≥ t/2 for t ≥ 2
-- statement:
--   Let $\lambda_0=0$ and $\lambda_t=\frac{1+\sqrt{1+4\lambda_{t-1}^2}}2$ for $t\ge1$. Then for every integer $t\ge2$,
--
--   $$\lambda_{t-1}\ge\frac t2.$$
--
--   Combined with the telescoped bound $\delta_t\le\frac\beta{2\lambda_{t-1}^2}\|u_1\|^2$, this gives the $2\beta\|x_1-x^*\|^2/t^2$ rate of Theorem 3.19.
--
--   **Formalization Note** The book states the bound without a range; at $t=1$ it would read $\lambda_0=0\ge\frac12$, which is false, so the statement is restricted to $t\ge2$, the range in which the proof uses it.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.19, p. 295 ("By induction it is easy to see that λ_{t−1} ≥ t/2")

import Mathlib
import Definitions.Def_ConvexOptAlg_NesterovSmooth_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovSmooth

/-- Growth of `λ` in the proof of Theorem 3.19 (Bubeck, arXiv:1405.4980v2, p. 295, "By induction it
is easy to see that λ_{t−1} ≥ t/2"), for every `t ≥ 2` (at `t = 1` the printed claim reads
`λ₀ = 0 ≥ 1/2`, which is false). -/
theorem lam_ge_half (t : ℕ) (ht : 2 ≤ t) : (t : ℝ) / 2 ≤ lam (t - 1) := by sorry

end ConvexOptAlg.NesterovSmooth

-- Prove2me | Theorems.Thm_BoydADMM_Nonconvex_boolean_projection
-- name    : BoydADMM.Nonconvex.boolean_projection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:07:02.180998+00:00
-- url     : https://prove2.me/theorems/44583149-8328-4380-a2de-e57a66e0b90f
-- title:
--   §9.1 — projection onto Boolean vectors by coordinatewise rounding
-- statement:
--   Let $v\in\mathbb R^n$. Round each entry independently to its nearest value in $\{0,1\}$, choosing zero when $v_i=1/2$, and call the resulting vector $w$. Then $w$ is Boolean and
--
--   $$\|w-v\|_2^2\le\|x-v\|_2^2\quad\text{for every }x\in\{0,1\}^n.$$
--
--   This is the exact Euclidean projection used for Boolean constraints in nonconvex ADMM.
--
--   **Formalization Note** At a tie, both zero and one are nearest; the chosen convention fixes a candidate without claiming uniqueness.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 74, §9.1, Boolean constraints bullet

import Mathlib
import Definitions.Def_BoydADMM_Nonconvex_ProjectionBasics

namespace BoydADMM.Nonconvex

/-- §9.1, p. 74: rounding each entry to a nearest Boolean value gives a
Euclidean projection onto the Boolean cube. -/
theorem boolean_projection {n : ℕ} (v : Fin n → ℝ) :
    roundBoolean v ∈ booleanSet ∧
    ∀ x ∈ booleanSet, sqDist (roundBoolean v) v ≤ sqDist x v := by sorry

end BoydADMM.Nonconvex

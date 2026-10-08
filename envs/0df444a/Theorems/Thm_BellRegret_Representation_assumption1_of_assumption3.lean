-- Prove2me | Theorems.Thm_BellRegret_Representation_assumption1_of_assumption3
-- name    : BellRegret.Representation.assumption1_of_assumption3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:21:23.18367+00:00
-- url     : https://prove2.me/theorems/2e2e29db-bb9d-4533-9171-a06cfc2cb362
-- title:
--   p. 969 — Assumption 1 is a special case of Assumption 3
-- statement:
--   Let $u(x,y)$ be a utility over final assets $x$ and foregone assets $y$ and $v$ a value function. If $u$ satisfies Assumption 3 (preferences between selecting one alternative over another and selecting a third over a fourth are invariant under shifting all outcomes by an equal incremental value), then $u$ satisfies Assumption 1 (the preferred alternative of a simple comparison is invariant under such shifts):
--   $$\text{Assumption 3}\;\Longrightarrow\;\text{Assumption 1}.$$
--   The paper obtains this by taking $L_3=L_2$ and $L_4=L_1$ in Assumption 3. It is what lets Theorem 1 use Lemmas 1 and 2, which are stated under Assumption 1, although Theorem 1 assumes only Assumptions 2 and 3.
--
--   **Formalization Note** No monotonicity hypothesis on $u$ or $v$ is needed, so none is assumed.
-- source:
--   Bell, Regret in Decision Making under Uncertainty, Operations Research 30(5) (1982) 961–981, p. 969 (PDF 10), sentence after Assumption 3

import Mathlib
import Definitions.Def_BellRegret_Representation_Model

namespace BellRegret.Representation

/-- Bell (1982), p. 969: Assumption 1 is a special case of Assumption 3 (take `L₃ = L₂`,
`L₄ = L₁`). -/
theorem assumption1_of_assumption3 (u : ℝ → ℝ → ℝ) (v : ℝ → ℝ)
    (hA3 : Assumption3 u v) : Assumption1 u v := by sorry

end BellRegret.Representation

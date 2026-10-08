-- Prove2me | Theorems.Thm_ExpConeIPM_Curvature_witness_mem
-- name    : ExpConeIPM.Curvature.witness_mem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:31.693896+00:00
-- url     : https://prove2.me/theorems/5b372064-25fb-43ad-b340-c0d3c7a49f9a
-- title:
--   §5, p. 356 — $\hat x = (1, e^{-2}, 0) \in \operatorname{int} K_{\exp}$ and $\hat u = (1,0,0) \in K_{\exp} \setminus \operatorname{int} K_{\exp}$
-- statement:
--   Let $K_{\exp} = \operatorname{cl}\{x \in \mathbb{R}^3 \mid x_1 \ge x_2 \exp(x_3/x_2),\ x_2 > 0\}$ be the exponential cone. The points
--
--   $$
--   \hat x := (1, e^{-2}, 0), \qquad \hat u := (1, 0, 0)
--   $$
--
--   satisfy $\hat x \in \operatorname{int}(K_{\exp})$ and $\hat u \in K_{\exp} \setminus \operatorname{int}(K_{\exp})$.
--
--   These are the base point and the direction at which Dahl and Andersen exhibit the failure of negative curvature for the exponential-cone barrier; the definition of negative curvature needs the base point in the interior of the cone and the direction in the cone.
--
--   **Formalization Note** The paper writes $\hat x \in K_{\exp}$; this statement asserts the stronger interior membership, which the definition of negative curvature requires and which holds since $1 > e^{-2}\exp(0)$. Coordinates are 0-based: the paper's $(x_1, x_2, x_3)$ are `(x 0, x 1, x 2)`.
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), p. 356, §5

import Mathlib
import Definitions.Def_ExpConeIPM_Curvature_ExpCone
import Definitions.Def_ExpConeIPM_Curvature_NegativeCurvature

open scoped InnerProductSpace

namespace ExpConeIPM.Curvature

/-- **§5, p. 356 — the witness.** `x̂ := (1, e^{−2}, 0)` lies in `int(Kexp)` (the paper writes
`x̂ ∈ Kexp`; the definition of negative curvature needs, and this states, the interior), and
`û := (1, 0, 0) ∈ Kexp \ int(Kexp)`. -/
theorem witness_mem :
    !₂[1, Real.exp (-2), 0] ∈ interior Kexp ∧
      !₂[(1 : ℝ), 0, 0] ∈ Kexp ∧ !₂[(1 : ℝ), 0, 0] ∉ interior Kexp := by sorry

end ExpConeIPM.Curvature

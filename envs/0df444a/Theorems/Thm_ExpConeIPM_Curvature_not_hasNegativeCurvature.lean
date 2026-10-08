-- Prove2me | Theorems.Thm_ExpConeIPM_Curvature_not_hasNegativeCurvature
-- name    : ExpConeIPM.Curvature.not_hasNegativeCurvature
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:26.400933+00:00
-- url     : https://prove2.me/theorems/d365c243-24a3-4c65-9163-f66ca438180d
-- title:
--   §5, p. 356 — the exponential-cone barrier does not have negative curvature
-- statement:
--   Let $K_{\exp} = \operatorname{cl}\{x \in \mathbb{R}^3 \mid x_1 \ge x_2\exp(x_3/x_2),\ x_2 > 0\}$ be the exponential cone and
--
--   $$
--   F(x) = -\log\bigl(x_2\log(x_1/x_2) - x_3\bigr) - \log x_1 - \log x_2
--   $$
--
--   its barrier (2). Then $F$ does **not** have negative curvature: it is not the case that
--
--   $$
--   F'''(x)[u] \preceq 0 \qquad \text{for all } x \in \operatorname{int}(K_{\exp}) \text{ and all } u \in K_{\exp},
--   $$
--
--   that is, there are $x \in \operatorname{int}(K_{\exp})$, $u \in K_{\exp}$ and $v \in \mathbb{R}^3$ with $\langle F'''(x)[u]\,v, v\rangle > 0$.
--
--   Barriers of symmetric cones have negative curvature, and barriers with negative curvature admit a unique scaling point satisfying one secant equation. The statement shows that the exponential cone falls outside this class, which is why Dahl and Andersen build their primal-dual scalings from Tunçel's framework instead.
--
--   **Formalization Note** $F'''(x)[u]$ is `fderiv ℝ (hess barrier) x u`, with the published Hessian `SelfScaledIPM.ShortStep.hess`, and the Loewner order is stated through the quadratic form. The direction $u$ ranges over the closed cone $K_{\exp}$, as in the paper; ranging over all of $\mathbb{R}^3$ would make the claim nearly free, since $F'''(x)[-u] = -F'''(x)[u]$.
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), p. 356, §5

import Mathlib
import Definitions.Def_ExpConeIPM_Curvature_ExpCone
import Definitions.Def_ExpConeIPM_Curvature_NegativeCurvature

open scoped InnerProductSpace

namespace ExpConeIPM.Curvature

/-- **§5, p. 356 (goal).** The exponential-cone barrier (2),
`F(x) = −log(x₂ log(x₁/x₂) − x₃) − log x₁ − log x₂`, does not have negative curvature on `Kexp`:
it is not true that `F'''(x)[u] ⪯ 0` for all `x ∈ int(Kexp)` and all `u ∈ Kexp`. -/
theorem not_hasNegativeCurvature : ¬ HasNegativeCurvature Kexp barrier := by sorry

end ExpConeIPM.Curvature

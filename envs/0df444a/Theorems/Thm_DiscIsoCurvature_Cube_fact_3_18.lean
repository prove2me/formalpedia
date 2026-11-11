-- Prove2me | Theorems.Thm_DiscIsoCurvature_Cube_fact_3_18
-- name    : DiscIsoCurvature.Cube.fact_3_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:07:24.610483+00:00
-- url     : https://prove2.me/theorems/9da1be27-69a9-42ce-9ffa-a669579fe8fa
-- title:
--   Fact 3.18 (Bobkov–Götze) — I(a)(I(b) − I(a) − I′(a)(b − a)) ≥ −(b − a)² for a ∈ (0, 1), b ∈ [0, 1]
-- statement:
--   Let $\mathcal I$ be the Gaussian isoperimetric profile ($\mathcal I=\varphi\circ\Phi^{-1}$ on $(0,1)$, $\mathcal I(0)=\mathcal I(1)=0$). For every $a\in(0,1)$ and $b\in[0,1]$,
--   $$\mathcal I(a)\big(\mathcal I(b)-\mathcal I(a)-\mathcal I'(a)(b-a)\big)\ge-(b-a)^2 .$$
--   This two-point inequality ([BG99, Eq. (3.9)]) is the scalar input of the local Bobkov inequality (Theorem 5.1).
--
--   Differences from the source:
--
--   - encoding: I′(a) → deriv gaussProfile a; reason: I is differentiable on (0, 1), so deriv is the derivative there
--   - encoding: I : [0, 1] → R≥0 → gaussProfile : ℝ → ℝ, 0 outside (0, 1); reason: only arguments in [0, 1] occur
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), p. 17, Fact 3.18

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_GaussProfile

namespace DiscIsoCurvature.Cube

/-- Fact 3.18 (Bobkov–Götze; p. 17): for `a ∈ (0, 1)` and `b ∈ [0, 1]`,
`I(a)(I(b) − I(a) − I′(a)(b − a)) ≥ −(b − a)²`, `I` the Gaussian isoperimetric profile. -/
theorem fact_3_18 (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    -(b - a) ^ 2 ≤
      gaussProfile a * (gaussProfile b - gaussProfile a - deriv gaussProfile a * (b - a)) := by sorry

end DiscIsoCurvature.Cube

-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_fiber_gate_pos
-- name    : BirkhoffGlobalSection.TangentialHessian.fiber_gate_pos
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-29T22:43:18.958999+00:00
-- url     : https://prove2.me/theorems/24ad27c4-9034-499a-8fc7-34fd9621747a
-- title:
--   Angle-free gate inequality for the Levi-Civita convexity of the restricted three-body problem
-- statement:
--   For
--   $$0 \le \mu \le \tfrac12, \qquad \tfrac{21}{10} \le c \le \tfrac{21}{10} + 10^{-6},$$
--   and $z \in \mathbb R^2$ with $2|z|^2 \le (3 - 2\mu)/5$, let $r = |2z^2 - 1| > 0$. Wherever the energy fiber over $z$ is non-empty, i.e. $F \ge 0$, the fiber gate data satisfy
--   $$G > 0 \qquad\text{and}\qquad F\,(\beta_1^2 + \beta_2^2) < G^2 .$$
--
--   Here $F$ is the squared fiber radius, $G$ the constant term minus the second-harmonic amplitude, and $\beta$ the first-harmonic coefficients of the bordered form of the Levi-Civita Hamiltonian on the fiber circle. By the general reduction theorem, this inequality implies the determinant clause of Joung–van Koert, Proposition 4.4. It is the angle-free gate inequality of Grisa (Zenodo 21270420, Theorem 3.7(b)).
--
--   Every quantity depends on $(\mu, c, |z|^2, z_1^2 - z_2^2, r)$ only. Numerically the minimum of $G - \sqrt{F}\,|\beta|$ over the domain is about $1.28$, attained at $\mu = \tfrac12$ on the axis $z_2 = 0$ with $|z|^2 \approx 0.09$. A rigorous proof requires a verified computation.
--
--   **Formalization note.** The phase point $s$ carries $z = (s_0, s_1)$; only $z$ enters. $G, F, \beta$ are `fibG`, `fibF`, `fibBeta1`, `fibBeta2`.
-- source:
--   Grisa, Exact fiber elimination for the Levi–Civita convexity gates of the planar restricted three-body problem, Zenodo 21270420 (2026), Theorem 3.7(b); the remaining numerical leaf of Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4.

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian_Fiber

namespace BirkhoffGlobalSection.TangentialHessian

/-- The `φ`-free gate inequality of the tangential-Hessian determinant (the remaining numerical leaf of
Proposition 4.4): on the subcritical window, wherever the fiber is non-empty, `fibG > 0` and
`fibF · (fibBeta1² + fibBeta2²) < fibG²`. -/
theorem fiber_gate_pos (μ c r : ℝ) (s : Phase)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000)
    (hr : 0 < r) (hr2 : r ^ 2 = secondCollisionDistanceSq s)
    (hz : 2 * zNormSq s ≤ (3 - 2 * μ) / 5) (hF : 0 ≤ fibF μ c r s) :
    0 < fibG μ c r s ∧
      fibF μ c r s * (fibBeta1 μ c r s ^ 2 + fibBeta2 μ c r s ^ 2) < fibG μ c r s ^ 2 := by sorry

end BirkhoffGlobalSection.TangentialHessian

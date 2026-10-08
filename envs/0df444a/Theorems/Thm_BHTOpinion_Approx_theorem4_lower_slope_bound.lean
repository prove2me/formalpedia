-- Prove2me | Theorems.Thm_BHTOpinion_Approx_theorem4_lower_slope_bound
-- name    : BHTOpinion.Approx.theorem4_lower_slope_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:03.567976+00:00
-- url     : https://prove2.me/theorems/f9f9d8df-cd76-4b0d-b93b-15c4b2156cd0
-- title:
--   Theorem 4, (3.7) left inequality — a solution from x̃_0 ∈ X_m^M has slope ≥ m e^{−t}: x_t ∈ X_{me^{−t}}
-- statement:
--   Let $m,M>0$ and let the initial opinion function $\tilde x_0$ lie in $X_m^M$. If $x$ is a solution of the continuum integral equation (3.2) with initial condition $\tilde x_0$, then for every $t\ge0$ and every $\alpha<\beta$ in $I=[0,1]$
--
--   $$m\,e^{-t}\,(\beta-\alpha)\le x_t(\beta)-x_t(\alpha),$$
--
--   that is, $\frac{x_t(\beta)-x_t(\alpha)}{\beta-\alpha}\ge m e^{-t}$ for $\beta\ne\alpha$.
--
--   This is the left inequality of (3.7) in Theorem 4. Section 4 uses it as "$x_t\in X_{me^{-t}}$ for all $t$": along the solution, Lemma 1 applies at every time with constant $2+8e^t/m$.
--
--   **Formalization Note** Theorem 4 asserts existence, uniqueness and the two-sided bound (3.7); only the lower bound, which the Section 4 argument uses, is stated here. The statement is about any solution of (3.2) from $\tilde x_0$ (Theorem 4 says there is exactly one). The upper bound $M e^{4t/m}$ of (3.7) is not included: its proof in Appendix B covers only an initial interval $[0,t_1]$.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, Continuous-time average-preserving opinion dynamics with opinion-dependent communications, SIAM J. Control Optim. 48 (2010), Theorem 4, (3.7) left inequality, p. 5225; used on p. 5231 (proof of Proposition 4)

import Mathlib
import Definitions.Def_BHTOpinion_Approx_Continuum

namespace BHTOpinion.Approx

theorem theorem4_lower_slope_bound (m M : ℝ) (hm : 0 < m) (hM : 0 < M) (x0 : ℝ → ℝ)
    (hx0m : BHTOpinion.Continuum.InXm m x0) (hx0M : BHTOpinion.Continuum.InXM M x0) (x : ℝ → ℝ → ℝ) (hx : BHTOpinion.Continuum.IsSolution x0 x) :
    ∀ t : ℝ, 0 ≤ t → ∀ α ∈ BHTOpinion.Continuum.I, ∀ β ∈ BHTOpinion.Continuum.I, α < β →
      m * Real.exp (-t) * (β - α) ≤ x t β - x t α := by sorry

end BHTOpinion.Approx

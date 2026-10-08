-- Prove2me | Theorems.Thm_BHTOpinion_Approx_proposition4_continuous_dependence
-- name    : BHTOpinion.Approx.proposition4_continuous_dependence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:57.503317+00:00
-- url     : https://prove2.me/theorems/f109ddcd-fe29-4f4d-a7d8-860dd1b32cc4
-- title:
--   Proposition 4 — continuous dependence on the initial condition near a regular x̃_0, uniformly on [0, T]
-- statement:
--   Let $m,M>0$, let $\tilde x_0\in X_m^M$ be a regular initial condition, and let $x$ be a solution of the continuum model (3.2) with initial condition $\tilde x_0$. Then for every $\varepsilon>0$ and every $T>0$ there exists $\delta>0$ with the following property: if $y$ is a solution of (3.2) with any initial condition $y_0\in Y$ such that $\|y_0-\tilde x_0\|_\infty\le\delta$, then
--
--   $$\|y_t-x_t\|_\infty\le\varepsilon\qquad\text{for all }t\in[0,T].$$
--
--   The number $\delta$ depends on $\tilde x_0$, $\varepsilon$ and $T$ but not on $y$. The perturbed initial condition $y_0$ need not be regular, nor even monotone; this is what allows step-function initial conditions coming from finitely many agents.
--
--   **Formalization Note** The sup norms over $I=[0,1]$ are written pointwise: $|y_0(\alpha)-\tilde x_0(\alpha)|\le\delta$ for all $\alpha\in I$, and $|y_t(\alpha)-x_t(\alpha)|\le\varepsilon$ for all $t\in[0,T]$ and $\alpha\in I$. "The solution" is read as any solution (Theorem 4 gives uniqueness). The page's "such if" is read as "such that if".
-- source:
--   Blondel, Hendrickx, Tsitsiklis, Continuous-time average-preserving opinion dynamics with opinion-dependent communications, SIAM J. Control Optim. 48 (2010), Proposition 4, p. 5231

import Mathlib
import Definitions.Def_BHTOpinion_Approx_Continuum

namespace BHTOpinion.Approx

theorem proposition4_continuous_dependence (m M : ℝ) (hm : 0 < m) (hM : 0 < M) (x0 : ℝ → ℝ)
    (hx0m : BHTOpinion.Continuum.InXm m x0) (hx0M : BHTOpinion.Continuum.InXM M x0) (x : ℝ → ℝ → ℝ) (hx : BHTOpinion.Continuum.IsSolution x0 x) :
    ∀ ε : ℝ, 0 < ε → ∀ T : ℝ, 0 < T → ∃ δ : ℝ, 0 < δ ∧
      ∀ (y0 : ℝ → ℝ) (y : ℝ → ℝ → ℝ), BHTOpinion.Continuum.IsSolution y0 y →
        (∀ α ∈ BHTOpinion.Continuum.I, |y0 α - x0 α| ≤ δ) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α ∈ BHTOpinion.Continuum.I, |y t α - x t α| ≤ ε := by sorry

end BHTOpinion.Approx

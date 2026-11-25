-- Prove2me | Theorems.Thm_Arxiv2405_15536_kappa_objective_least_squares_limit
-- name    : Arxiv2405_15536.kappa_objective_least_squares_limit
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T18:26:55.885634+00:00
-- url     : https://prove2.me/theorems/d21d80a6-191d-55ba-b05b-a981c4dbd8fa
-- title:
--   Eq. (12) $\to$ Eq. (1): the $\kappa$-objective converges to least squares as $\kappa\to0$
-- statement:
--   Let $S$ and $R$ be finite sets of sources and receivers, $T\in\mathbb{R}$, and let $\varepsilon_{s,r}:[0,T]\to\mathbb{R}$ be residual traces with $\int_0^T\varepsilon_{s,r}(t)^2\,dt<\infty$ for all $s,r$. Then the κ-objective function (12) converges to the least-squares objective (1):
--
--   $$\lim_{\kappa\to0}\Big(-\sum_{s,r}\int_0^T\ln\big[\exp_\kappa\big(-\beta_\kappa\varepsilon_{s,r}(t)^2\big)\big]dt\Big)=\frac12\sum_{s,r}\int_0^T\varepsilon_{s,r}(t)^2\,dt.$$
--
--   **Formalization Note** The square-integrability of the residuals is the standing assumption under which $\phi_0$ in eq. (1) is finite; Lean's integral of a non-integrable function is $0$, so it is stated as a hypothesis. The limit is over $\kappa\to0$, $\kappa\neq0$. The residual traces are arbitrary; the model $m$ enters only through them.
-- source:
--   da Silva and Kaniadakis, A graph-space optimal transport FWI approach based on kappa-generalized Gaussian distribution, arXiv:2405.15536v1 (2024), claim c004; Sec. 2.2, text after eq. (12), with eq. (1) of Sec. 2.1, PDF p. 4 (eq. (1) on p. 2)

import Mathlib
import Definitions.Def_Arxiv2405_15536_Basic

open MeasureTheory Filter Topology Asymptotics

namespace Arxiv2405_15536

theorem kappa_objective_least_squares_limit {S R : Type*} [Fintype S] [Fintype R] (T : ℝ)
    (e : S → R → ℝ → ℝ) (he : ∀ s r, IntegrableOn (fun t => e s r t ^ 2) (Set.Icc 0 T)) :
    Tendsto (fun κ => phiKappa κ T e) (𝓝[≠] 0) (𝓝 (phi0 T e)) := by sorry

end Arxiv2405_15536

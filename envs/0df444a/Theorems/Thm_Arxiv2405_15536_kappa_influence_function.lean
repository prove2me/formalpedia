-- Prove2me | Theorems.Thm_Arxiv2405_15536_kappa_influence_function
-- name    : Arxiv2405_15536.kappa_influence_function
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T18:31:13.650015+00:00
-- url     : https://prove2.me/theorems/0d5efd1b-3c21-5856-b782-82bc2d08b722
-- title:
--   Eq. (14): the influence function of the $\kappa$-objective
-- statement:
--   For a single residual $\varepsilon$, let $\Upsilon_\kappa(\varepsilon)$ be the derivative of $\varepsilon\mapsto-\ln\exp_\kappa(-\beta_\kappa\varepsilon^2)$ (eq. 13). Then this function is differentiable at every $\varepsilon\in\mathbb{R}$, and
--
--   $$\Upsilon_\kappa(\varepsilon)=\begin{cases}\dfrac{2\beta_\kappa\varepsilon}{\sqrt{1+\kappa^2\beta_\kappa^2\varepsilon^4}}, & 0<\kappa<2/3,\\[2mm] \varepsilon, & \kappa=0.\end{cases}$$
--
--   **Formalization Note** The case $\kappa=0$ uses $\exp_0=\exp$ and $\beta_0=1/2$, as in the paper.
-- source:
--   da Silva and Kaniadakis, A graph-space optimal transport FWI approach based on kappa-generalized Gaussian distribution, arXiv:2405.15536v1 (2024), claim c005; Sec. 2.2, eqs. (13)-(14), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv2405_15536_Basic

open MeasureTheory Filter Topology Asymptotics

namespace Arxiv2405_15536

theorem kappa_influence_function :
    (∀ κ : ℝ, 0 < κ → κ < 2 / 3 → ∀ ε : ℝ, HasDerivAt (lossKappa κ)
      (2 * betaKappa κ * ε / Real.sqrt (1 + κ ^ 2 * betaKappa κ ^ 2 * ε ^ 4)) ε) ∧
    (∀ ε : ℝ, HasDerivAt (lossKappa 0) ε ε) := by sorry

end Arxiv2405_15536

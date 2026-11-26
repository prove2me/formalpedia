-- Prove2me | Theorems.Thm_Arxiv2405_15536_kappa_objective_robust
-- name    : Arxiv2405_15536.kappa_objective_robust
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T18:32:36.267252+00:00
-- url     : https://prove2.me/theorems/2097a0cb-548f-4dab-af7f-e09d3448a4f8
-- title:
--   Eq. (14), Sec. 2.2: the $\kappa$-objective is robust for $0<\kappa<2/3$, least squares is not
-- statement:
--   Let $\Upsilon_\kappa$ be the influence function of the κ-objective (eq. 13). Then:
--
--   1. for every $0<\kappa<2/3$, $\Upsilon_\kappa(\varepsilon)\to0$ as $\varepsilon\to+\infty$ and as $\varepsilon\to-\infty$, so the κ-objective function is robust to outliers in Hampel's sense;
--   2. for $\kappa=0$ (least squares), $\Upsilon_0(\varepsilon)\to+\infty$ as $\varepsilon\to+\infty$ and $\Upsilon_0(\varepsilon)\to-\infty$ as $\varepsilon\to-\infty$, so the conventional objective is non-robust.
--
--   This is the paper's justification that the κ-objective function is outlier-resistant.
--
--   **Formalization Note** The paper says the influence function "tends to infinity in the limit $\kappa\to0$"; what eq. (14) gives, and what is stated, is the divergence at $\kappa=0$ itself. For each fixed $\kappa>0$ the influence function tends to $0$.
-- source:
--   da Silva and Kaniadakis, A graph-space optimal transport FWI approach based on kappa-generalized Gaussian distribution, arXiv:2405.15536v1 (2024), claim c006; Sec. 2.2, text around eqs. (13)-(14), PDF p. 4

import Mathlib
import Definitions.Def_Arxiv2405_15536_Basic

open MeasureTheory Filter Topology Asymptotics

namespace Arxiv2405_15536

theorem kappa_objective_robust :
    (∀ κ : ℝ, 0 < κ → κ < 2 / 3 → IsRobust (influence κ)) ∧ IsNonRobust (influence 0) := by sorry

end Arxiv2405_15536

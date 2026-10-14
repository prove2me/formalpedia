-- Prove2me | Theorems.Thm_BBDisclosure_Total_equation_14
-- name    : BBDisclosure.Total.equation_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:23:28.840626+00:00
-- url     : https://prove2.me/theorems/7d545956-3239-47a5-8da0-955ff00922af
-- title:
--   (14), p. 8518 — BBD, region 1: $E(\pi_{a2})$ as a function of $x_1$ and the four thresholds
-- statement:
--   Consider the second period under behavior-based disclosure, at share $x_1\in(0,1)$ and cost $0<c<5/36$. Let a second-period equilibrium have thresholds $\hat q_{ao},\hat q_{an},\hat q_{bo},\hat q_{bn}$, and suppose every belief pair on its support lies in region 1 of Lemma 2, i.e. $\tfrac12-\hat q_{bn}/8<x_1<\tfrac12+\hat q_{an}/8$. Then firm A's ex ante second-period profit is
--
--   $$E(\pi_{a2})=\frac{(1+2x_1)^2+(3-4x_1)^2}{18}+\frac{4-\hat q_{ao}^{\,3}-\hat q_{an}^{\,3}-\hat q_{bo}^{\,3}-\hat q_{bn}^{\,3}}{216}-c\big[1-x_1\hat q_{ao}-(1-x_1)\hat q_{an}\big].$$
--
--   Its dependence on $x_1$ (directly and through all four thresholds) drives the first-order condition behind (17).
--
--   **Formalization Note.** Stated in terms of the equilibrium thresholds rather than after substituting (13). "In region 1" is read as the support condition above. $0<c<5/36$ is the standing assumption (p. 8515).
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8518, equation (14)

import Mathlib
import Definitions.Def_BBDisclosure_Total_Stage2

namespace BBDisclosure.Total

/-- (14), p. 8518: in region 1, firm A's ex ante second-period profit under behavior-based
disclosure. -/
theorem equation_14 (c x1 : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) (hx0 : 0 < x1) (hx1 : x1 < 1)
    (e : BBDisclosure.Stage2.ProfileBBD) (he : BBDisclosure.Stage2.IsStage2EqBBD c x1 e) (hreg : BBDisclosure.Stage2.SupportRegion1BBD x1 e) :
    BBDisclosure.Stage2.exAnteA_BBD c x1 e =
      ((1 + 2 * x1) ^ 2 + (3 - 4 * x1) ^ 2) / 18
        + (4 - e.qao ^ 3 - e.qan ^ 3 - e.qbo ^ 3 - e.qbn ^ 3) / 216
        - c * (1 - x1 * e.qao - (1 - x1) * e.qan) := by sorry

end BBDisclosure.Total

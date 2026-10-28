-- Prove2me | Theorems.Thm_BBDisclosure_Total_equation_5
-- name    : BBDisclosure.Total.equation_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:23:36.400031+00:00
-- url     : https://prove2.me/theorems/ace86943-3ddd-4187-ae18-54ccd5041abe
-- title:
--   (5), p. 8516 — uniform disclosure, region 1: $E(\pi_{a2})$ as a function of $x_1$ and the thresholds
-- statement:
--   Consider the second period under uniform disclosure, at first-period share $x_1\in(0,1)$ and unit disclosure cost $0<c<5/36$. Let a second-period equilibrium have thresholds $\hat q_a,\hat q_b$, and suppose every belief pair on its support lies in region 1 of Lemma 1, i.e. $\tfrac12-\hat q_b/8<x_1<\tfrac12+\hat q_a/8$. Then firm A's ex ante second-period profit is
--
--   $$E(\pi_{a2})=\frac{(1+2x_1)^2+(3-4x_1)^2}{18}+\frac{2-\hat q_a^{\,3}-\hat q_b^{\,3}}{108}-c(1-\hat q_a).$$
--
--   This is the second-period value function that firms take into account when they choose first-period prices; differentiating it in $x_1$ (with the thresholds moving with $x_1$) leads to (9).
--
--   **Formalization Note.** The paper substitutes the equilibrium threshold (4) into $E(\pi_{a2})$; the identity holds for the equilibrium thresholds, whatever their value, so it is stated in terms of $\hat q_a,\hat q_b$. "In region 1" is read as the support condition above (on every realized belief pair, not only on one). $0<c<5/36$ is the paper's standing assumption (p. 8515).
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8516, equation (5)

import Mathlib
import Definitions.Def_BBDisclosure_Total_Stage2

namespace BBDisclosure.Total

/-- (5), p. 8516: in region 1, firm A's ex ante second-period profit under uniform disclosure. -/
theorem equation_5 (c x1 : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36) (hx0 : 0 < x1) (hx1 : x1 < 1)
    (e : BBDisclosure.Stage2.ProfileU) (he : BBDisclosure.Stage2.IsStage2EqU c x1 e) (hreg : BBDisclosure.Stage2.SupportRegion1U x1 e) :
    BBDisclosure.Stage2.exAnteA_U c x1 e =
      ((1 + 2 * x1) ^ 2 + (3 - 4 * x1) ^ 2) / 18 + (2 - e.qa ^ 3 - e.qb ^ 3) / 108
        - c * (1 - e.qa) := by sorry

end BBDisclosure.Total

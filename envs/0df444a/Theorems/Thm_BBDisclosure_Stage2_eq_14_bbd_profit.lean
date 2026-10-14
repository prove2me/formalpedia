-- Prove2me | Theorems.Thm_BBDisclosure_Stage2_eq_14_bbd_profit
-- name    : BBDisclosure.Stage2.eq_14_bbd_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:57.440342+00:00
-- url     : https://prove2.me/theorems/bdfe3a04-ebf5-4b5c-9470-1bf6e7621d5f
-- title:
--   (14), p. 8518 — the BBD ex ante second-period profit E(π_a2)
-- statement:
--   Under behavior-based disclosure, let $0<c<5/36$ and $0<x_1<1$, and take any second-period equilibrium with thresholds $\hat q_{ao},\hat q_{an},\hat q_{bo},\hat q_{bn}$ satisfying the region-1 support condition $1/2-\hat q_{bn}/8<x_1<1/2+\hat q_{an}/8$. Then firm A's ex ante second-period profit is
--   $$E(\pi_{a2})=\frac{(1+2x_1)^2+(3-4x_1)^2}{18}+\frac{4-\hat q_{ao}^3-\hat q_{an}^3-\hat q_{bo}^3-\hat q_{bn}^3}{216}-c\big[1-x_1\hat q_{ao}-(1-x_1)\hat q_{an}\big].$$
--
--   Compared with (5), the expected disclosure cost is now split by segment: A pays $x_1c$ with probability $1-\hat q_{ao}$ and $(1-x_1)c$ with probability $1-\hat q_{an}$.
--
--   **Formalization Note** "In region 1" is read as the support window (see the model). $E(\pi_{a2})$ is the double integral over $(q_a,q_b)\in[0,1]^2$ of A's ex post profit (10).
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8518, (14)

import Mathlib
import Definitions.Def_BBDisclosure_Stage2_Model

namespace BBDisclosure.Stage2

theorem eq_14_bbd_profit (c x1 : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36)
    (hx : x1 ∈ Set.Ioo (0 : ℝ) 1) (e : ProfileBBD)
    (he : IsStage2EqBBD c x1 e) (hreg : SupportRegion1BBD x1 e) :
    exAnteA_BBD c x1 e = ((1 + 2 * x1) ^ 2 + (3 - 4 * x1) ^ 2) / 18
      + (4 - e.qao ^ 3 - e.qan ^ 3 - e.qbo ^ 3 - e.qbn ^ 3) / 216
      - c * (1 - x1 * e.qao - (1 - x1) * e.qan) := by sorry

end BBDisclosure.Stage2

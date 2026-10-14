-- Prove2me | Theorems.Thm_BBDisclosure_Stage2_eq_5_uniform_profit
-- name    : BBDisclosure.Stage2.eq_5_uniform_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:50.100877+00:00
-- url     : https://prove2.me/theorems/2d9d4bd4-e7c4-4354-899c-fb7271487f6d
-- title:
--   (5), p. 8516 — the uniform-disclosure ex ante second-period profit E(π_a2)
-- statement:
--   Under uniform disclosure, let $0<c<5/36$ and $0<x_1<1$, and take any second-period equilibrium with thresholds $\hat q_a,\hat q_b$ satisfying the region-1 support condition $1/2-\hat q_b/8<x_1<1/2+\hat q_a/8$. Then firm A's ex ante second-period profit is
--   $$E(\pi_{a2})=\frac{(1+2x_1)^2+(3-4x_1)^2}{18}+\frac{2-\hat q_a^3-\hat q_b^3}{108}-c(1-\hat q_a).$$
--
--   The last term is the expected disclosure cost: A discloses to the whole line, at cost $c$, with probability $1-\hat q_a$. This formula is the benchmark against which behavior-based disclosure is compared.
--
--   **Formalization Note** "In region 1" is read as the support window (see the model). $E(\pi_{a2})$ is the double integral over $(q_a,q_b)\in[0,1]^2$ of A's ex post profit at the equilibrium prices and beliefs.
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8516, (5)

import Mathlib
import Definitions.Def_BBDisclosure_Stage2_Model

namespace BBDisclosure.Stage2

theorem eq_5_uniform_profit (c x1 : ℝ) (hc0 : 0 < c) (hc : c < 5 / 36)
    (hx : x1 ∈ Set.Ioo (0 : ℝ) 1) (e : ProfileU)
    (he : IsStage2EqU c x1 e) (hreg : SupportRegion1U x1 e) :
    exAnteA_U c x1 e = ((1 + 2 * x1) ^ 2 + (3 - 4 * x1) ^ 2) / 18
      + (2 - e.qa ^ 3 - e.qb ^ 3) / 108 - c * (1 - e.qa) := by sorry

end BBDisclosure.Stage2

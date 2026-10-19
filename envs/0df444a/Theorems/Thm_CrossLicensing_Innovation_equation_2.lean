-- Prove2me | Theorems.Thm_CrossLicensing_Innovation_equation_2
-- name    : CrossLicensing.Innovation.equation_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T13:00:00.719002+00:00
-- url     : https://prove2.me/theorems/3a10f165-6320-4c95-9679-c787355be9b3
-- title:
--   Display (2), p. 10 — the Cournot quantities are the unique equilibrium of the quantity game (symmetric form)
-- statement:
--   Let $0 \le \beta \le 1$, innovation levels $T_1, T_2 \ge 0$ and a wholesale price $r \ge 0$. In the quantity game (1), where $M_i$ chooses $q_i \ge 0$ to maximize $(1 + T_i + \beta T_j - q_i - q_j - r)q_i$, the Cournot quantities of display (2) below are nonnegative, and a profile $(q_1, q_2)$ of nonnegative quantities is a pure Nash equilibrium if and only if it equals them:
--
--   $$(q_1, q_2) = \begin{cases} \big(\tfrac13(2a - b - r),\ \tfrac13(2b - a - r)\big), & r \le 2\min(a,b) - \max(a,b),\\ \text{only the larger of } a, b \text{ sells } \tfrac12(\max(a,b) - r), & 2\min(a,b) - \max(a,b) < r \le \max(a,b),\\ (0,0), & \text{otherwise},\end{cases}$$
--
--   where $a = 1 + T_1 + \beta T_2$, $b = 1 + T_2 + \beta T_1$ (manufacturer 2 sells alone on ties $a = b$).
--
--   The theorem justifies substituting display (2) into the supplier's problem: the downstream equilibrium exists and is unique for every price.
--
--   **Formalization Note** The paper writes (2) for $T_2 \ge T_1$; then $a \le b$, the threshold $2a - b$ is the paper's $r_1$ and $b$ is $r_2$. The symmetric form is needed because the innovation game evaluates profiles with $T_1 > T_2$.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), p. 10, display (2)

import Mathlib
import Definitions.Def_CrossLicensing_Innovation_Model

namespace CrossLicensing.Innovation

theorem equation_2 (β T1 T2 r : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hT1 : 0 ≤ T1)
    (hT2 : 0 ≤ T2) (hr : 0 ≤ r) :
    0 ≤ (quantities β T1 T2 r).1 ∧ 0 ≤ (quantities β T1 T2 r).2 ∧
    ∀ q1 q2 : NNReal,
      IsQuantityEquilibrium β T1 T2 r q1 q2 ↔ ((q1 : ℝ), (q2 : ℝ)) = quantities β T1 T2 r := by sorry

end CrossLicensing.Innovation

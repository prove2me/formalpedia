-- Prove2me | Theorems.Thm_BondVoting_Sybil_proposition_2
-- name    : BondVoting.Sybil.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:43.202024+00:00
-- url     : https://prove2.me/theorems/39da397d-50d0-48ec-873c-05aa51e1ffa2
-- title:
--   Proposition 2, p. 24 — bond voting is robustly v-implementable
-- statement:
--   Let the voting bond rate be $r > 0$ and the commitment horizon $T > 0$. Then bond voting is robustly v-implementable:
--
--   1. the bond vote function $v(q, t) = q e^{rt}$ ($t > 0$), $v(q, 0) = 0$, values commitment (Definition 2);
--   2. it has non-increasing influence of tokens (Definition 3);
--   3. for every admissible agent type $(\theta, u, r_i)$ — that is, $|u|\theta > 1$ and $r_i > r$ — the bond-voting payoff
--   $$\pi_i(q, t) = |u|\theta\, q\, e^{rt} - q\,(e^{r_i t} - 1) \quad (t > 0), \qquad \pi_i(q, 0) = 0,$$
--   is Sybil resistant (Definition 6): for no budget $q > 0$ is there a split $q_1, \dots, q_M \ge 0$, $\sum_m q_m \le q$, with commitments $t_1, \dots, t_M \in (0, T]$ such that $\sum_m \pi_i(q_m, t_m) > \pi_i(q, t)$ for every single-entity commitment $t \in [0, T]$.
--
--   This is the main result of the paper: time-weighted voting through bonds rewards commitment, does not reward concentrated token holdings more than linearly, and gives no agent a reason to create multiple identities.
--
--   **Formalization Note.** The hypothesis $r > 0$ is added (the paper does not state the sign of $r$; Definition 2 fails for $r \le 0$). Sybil resistance compares an attack with every commitment the agent could choose as a single entity, not with a fixed one or with the formula $t^*_i$; this keeps the statement meaningful for agent types with $r_i \ge \theta|u| r$, for which equation (6) gives no maximizer.
-- source:
--   Mohan, Khezr & Berg, Voting with time commitment for decentralized governance: Bond voting as a Sybil-resistant mechanism, SSRN 4259599 (PDF of 2024-02-20), p. 24, Proposition 2 (proof pp. 24–25)

import Mathlib
import Definitions.Def_BondVoting_Sybil_Model

namespace BondVoting.Sybil
theorem proposition_2 (r T : ℝ) (hr : 0 < r) (hT : 0 < T) :
    RobustlyVImplementable (bondVote r) (bondPayoffs r) T := by sorry
end BondVoting.Sybil

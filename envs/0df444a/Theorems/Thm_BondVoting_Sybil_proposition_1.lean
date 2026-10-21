-- Prove2me | Theorems.Thm_BondVoting_Sybil_proposition_1
-- name    : BondVoting.Sybil.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:44.711245+00:00
-- url     : https://prove2.me/theorems/a181c032-d8e5-4ef2-b0d2-ef597a65d74d
-- title:
--   Proposition 1 (cases 1–2), p. 23 — the optimal bond length
-- statement:
--   Let $r > 0$ be the voting bond rate and $T > 0$ the horizon, and let an agent of type $(\theta, u, r_i)$ satisfy $|u|\theta > 1$ and $r_i > r$, with budget $q > 0$. Suppose
--   $$r_i < \theta|u|\, r,$$
--   and let $t^*_i$ be given by equation (6). Then:
--
--   1. if $r_i \le \frac{\theta|u|}{e^{T(r_i - r)}}\, r$, then $t^*_i = T$;
--   2. if $\frac{\theta|u|}{e^{T(r_i - r)}}\, r < r_i$, then $t^*_i = \frac{\ln(\theta|u| r / r_i)}{r_i - r}$ and $t^*_i < T$;
--   3. $t^*_i \in (0, T]$, and $t^*_i$ is the unique maximizer of the payoff over the agent's choices: $\pi_i(q, t) < \pi_i(q, t^*_i)$ for every $t \in [0, T]$ with $t \ne t^*_i$.
--
--   This identifies the bond length an agent buys, and shows that it does not depend on her budget $q$ — the fact Proposition 2 uses to rule out profitable Sybil attacks.
--
--   **Formalization Note.** Only the first two cases of (6) are stated; their union is $r_i < \theta|u| r$, since $e^{T(r_i - r)} > 1$. The third case ($t^*_i = 0$ when $r_i \ge \theta|u| r$) is not stated: there the payoff $q(\theta|u| e^{rt} - e^{r_i t} + 1)$ tends to $\theta|u| q > 0$ as $t \to 0^+$ while it equals $0$ at $t = 0$, so no maximizer exists. The hypothesis $r > 0$ is the mission-wide addition (it is implied here by $r < r_i < \theta|u| r$).
-- source:
--   Mohan, Khezr & Berg, Voting with time commitment for decentralized governance: Bond voting as a Sybil-resistant mechanism, SSRN 4259599 (PDF of 2024-02-20), p. 23, Proposition 1, equation (6), cases 1–2

import Mathlib
import Definitions.Def_BondVoting_Sybil_Model

namespace BondVoting.Sybil
theorem proposition_1 (r θ u ri T q : ℝ) (hr : 0 < r) (hT : 0 < T)
    (hadm : Admissible r θ u ri) (hq : 0 < q) (hint : ri < θ * |u| * r) :
    (ri ≤ θ * |u| / Real.exp (T * (ri - r)) * r → tStar r θ u ri T = T) ∧
    (θ * |u| / Real.exp (T * (ri - r)) * r < ri →
      tStar r θ u ri T = Real.log (θ * |u| * r / ri) / (ri - r) ∧ tStar r θ u ri T < T) ∧
    tStar r θ u ri T ∈ Set.Ioc 0 T ∧
    ∀ t ∈ Set.Icc 0 T, t ≠ tStar r θ u ri T →
      bondPayoff r θ u ri q t < bondPayoff r θ u ri q (tStar r θ u ri T) := by sorry
end BondVoting.Sybil

-- Prove2me | Theorems.Thm_BondVoting_Sybil_bondVote_properties
-- name    : BondVoting.Sybil.bondVote_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:42.178992+00:00
-- url     : https://prove2.me/theorems/f26c846d-072d-432c-8910-8602b35ed2ea
-- title:
--   Proof of Proposition 2, p. 24 — the bond vote function values commitment and has non-increasing influence of tokens
-- statement:
--   Let the voting bond rate be $r > 0$ and the horizon $T > 0$. The bond vote function
--   $$v(q, t) = \frac{q}{P_t} = q\, e^{rt} \quad (t > 0), \qquad v(q, 0) = 0,$$
--   values commitment and has non-increasing influence of tokens: for every $q > 0$ and $t \in (0, T]$,
--   $$\frac{\partial v}{\partial t}(q,t) > 0, \qquad \frac{\partial v}{\partial q}(q,t) > 0, \qquad \frac{\partial^2 v}{\partial q^2}(q,t) \le 0.$$
--
--   These are the first two of the three requirements of robust v-implementability (Definition 7).
--
--   **Formalization Note.** The hypothesis $r > 0$ is added: the paper never states the sign of $r$, but $\partial v/\partial t = r q e^{rt}$ is positive only when $r > 0$ (the paper's examples use $r = 0.05$ and $r = 0.03$).
-- source:
--   Mohan, Khezr & Berg, Voting with time commitment for decentralized governance: Bond voting as a Sybil-resistant mechanism, SSRN 4259599 (PDF of 2024-02-20), p. 24, proof of Proposition 2

import Mathlib
import Definitions.Def_BondVoting_Sybil_Model

namespace BondVoting.Sybil
theorem bondVote_properties (r T : ℝ) (hr : 0 < r) (hT : 0 < T) :
    ValuableCommitment (bondVote r) T ∧ NonIncreasingInfluence (bondVote r) T := by sorry
end BondVoting.Sybil

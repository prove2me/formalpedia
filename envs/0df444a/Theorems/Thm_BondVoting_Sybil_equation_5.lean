-- Prove2me | Theorems.Thm_BondVoting_Sybil_equation_5
-- name    : BondVoting.Sybil.equation_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:41.154688+00:00
-- url     : https://prove2.me/theorems/47a6cd04-5de8-4247-b52d-bf46414f41f6
-- title:
--   Equation (5), p. 22 — the bond-voting payoff in closed form
-- statement:
--   Let $r$ be the voting bond rate, and consider an agent of type $(\theta, u, r_i)$ with budget $q$ who commits for time $t > 0$. Then she casts $V = q e^{rt}$ votes, and her payoff (4) equals
--   $$\pi_i(q, t) = |u|\theta\, q\, e^{rt} - q\,\bigl(e^{r_i t} - 1\bigr).$$
--
--   The benefit $|u|\theta q e^{rt}$ grows with the vote, and the cost $q(e^{r_i t} - 1)$ is the forgone outside return on the staked tokens. This closed form is linear in $q$ for each fixed $t > 0$, which is what connects bond voting to Theorem 1.
-- source:
--   Mohan, Khezr & Berg, Voting with time commitment for decentralized governance: Bond voting as a Sybil-resistant mechanism, SSRN 4259599 (PDF of 2024-02-20), p. 22, equation (5)

import Mathlib
import Definitions.Def_BondVoting_Sybil_Model

namespace BondVoting.Sybil
theorem equation_5 (r θ u ri q t : ℝ) (ht : 0 < t) :
    bondVote r q t = q * Real.exp (r * t) ∧
      bondPayoff r θ u ri q t = |u| * θ * q * Real.exp (r * t) - q * (Real.exp (ri * t) - 1) := by sorry
end BondVoting.Sybil

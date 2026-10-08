-- Prove2me | Theorems.Thm_AstromPOMDP_Bounds_theorem_4
-- name    : AstromPOMDP.Bounds.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:17:03.246951+00:00
-- url     : https://prove2.me/theorems/d991c76b-04eb-4822-b1f3-fff985f0a65b
-- title:
--   Theorem 4 — complete-information value is a lower bound
-- statement:
--   Let $w$ be any probability distribution over the hidden states at stage $k$, with $1\le k\le N$. For the general observation matrix $Q$, let $V_k(w)$ solve the partial-observation recursion (3.28), and let $V'_k(w)=\sum_i S_k(i)w_i$, where $S$ solves the complete-information recursion (5.4). Then
--   $$V'_k(w)\le V_k(w).$$
--
--   The complete-information value supplies the lower side of the information bound. The special case of exact measurements motivates $V'$ but is not a hypothesis of the inequality.
-- source:
--   Åström, Optimal Control of Markov Processes with Incomplete State Information, J. Math. Anal. Appl. 10(1):174–205 (1965), https://doi.org/10.1016/0022-247X(65)90154-X, p. 191, Theorem 4, (5.10)

import Definitions.Def_AstromPOMDP_Bounds_Model

namespace AstromPOMDP.Bounds

variable {St Obs : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
  [Fintype Obs] [DecidableEq Obs] [Nonempty Obs]
  {d N : ℕ} [NeZero N]

/-- Åström, *Optimal Control of Markov Processes with Incomplete State Information*,
J. Math. Anal. Appl. 10 (1965), Theorem 4, p. 191, (5.10).

`Vprime` is the linear extension (5.3) of the complete-information recursion
(5.4). The observation matrix here is arbitrary. -/
theorem theorem_4 (m : Model St Obs d N) :
    ∀ t, 1 ≤ t → t ≤ N → ∀ w, IsBelief w → Vprime m t w ≤ V m t w := by sorry

end AstromPOMDP.Bounds

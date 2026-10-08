-- Prove2me | Theorems.Thm_AstromPOMDP_Bounds_theorem_5
-- name    : AstromPOMDP.Bounds.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:17:13.696822+00:00
-- url     : https://prove2.me/theorems/96c33511-0507-4e10-b394-35d876b93f16
-- title:
--   Theorem 5 — open-loop value is an upper bound
-- statement:
--   Let $w$ be any probability distribution over the hidden states at stage $k$, with $1\le k\le N$. For the general observation matrix $Q$, let $V_k(w)$ solve the partial-observation recursion (3.28), and let $V''_k(w)$ solve the open-loop recursion (5.7). Then
--   $$V_k(w)\le V''_k(w).$$
--
--   An open-loop schedule can ignore later observations, so this is the upper side of the information bound. The special constant-row observation model motivates $V''$ but is not a hypothesis of the theorem.
-- source:
--   Åström, Optimal Control of Markov Processes with Incomplete State Information, J. Math. Anal. Appl. 10(1):174–205 (1965), https://doi.org/10.1016/0022-247X(65)90154-X, p. 192, Theorem 5, (5.11)

import Definitions.Def_AstromPOMDP_Bounds_Model

namespace AstromPOMDP.Bounds

variable {St Obs : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
  [Fintype Obs] [DecidableEq Obs] [Nonempty Obs]
  {d N : ℕ} [NeZero N]

/-- Åström, *Optimal Control of Markov Processes with Incomplete State Information*,
J. Math. Anal. Appl. 10 (1965), Theorem 5, p. 192, (5.11).

`Vdouble` is the open-loop recursion (5.7). The observation matrix is
arbitrary; the equal-row case (5.5) only motivates the comparison. -/
theorem theorem_5 (m : Model St Obs d N) :
    ∀ t, 1 ≤ t → t ≤ N → ∀ w, IsBelief w → V m t w ≤ Vdouble m t w := by sorry

end AstromPOMDP.Bounds

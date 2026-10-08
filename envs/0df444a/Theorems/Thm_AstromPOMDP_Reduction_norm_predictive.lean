-- Prove2me | Theorems.Thm_AstromPOMDP_Reduction_norm_predictive
-- name    : AstromPOMDP.Reduction.norm_predictive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:43:33.083232+00:00
-- url     : https://prove2.me/theorems/b08fa85c-f668-4943-a31e-41ebbfbc7d7a
-- title:
--   §III.B, p. 183 — ‖z^j(u, w(t))‖ = P[y_{t+1} = j | η(t)]
-- statement:
--   Let $c$ be an admissible control law, $t\ge1$ with $t+1\le N$, and $\eta(t)$ outputs with $P(\eta(t))>0$. Let $w(t)$ be the conditional distribution of $x_t$ given $\eta(t)$ and $u(t)=c(\eta(t),t)$. Then for every output $j$
--   $$
--   \frac{P(y_1=\eta_1,\dots,y_t=\eta_t,\ y_{t+1}=j)}{P(y_1=\eta_1,\dots,y_t=\eta_t)}=\|z^j(u(t),w(t))\|=\sum_i\Big|\sum_s q_{ij}\,p_{si}(u(t),t+1)\,w_s(t)\Big| ,
--   $$
--   both probabilities being computed from the joint law of states and outputs.
--
--   This is the paper's "physical interpretation" of the norm: the weights $\|z^j\|$ in the functional equation (3.28) are the predictive probabilities of the next output.
-- source:
--   Åström, Optimal Control of Markov Processes with Incomplete State Information, J. Math. Anal. Appl. 10(1):174–205 (1965), DOI 10.1016/0022-247X(65)90154-X, p. 183, §III.B (after (3.25))

import Mathlib
import Definitions.Def_AstromPOMDP_Reduction_Belief

namespace AstromPOMDP.Reduction

/-- Åström (1965), J. Math. Anal. Appl. 10:174–205, §III.B, p. 183 (after (3.25)): the norm
`‖z^j‖` is the conditional probability `P[y(t + 1) = j | y₁ = η₁, …, y_t = η_t]`. For an admissible
control law `c`, outputs `η = (η₁, …, η_{n+1})` of positive probability with `n + 2 ≤ N`, and any
output `j`,
`P(η₁, …, η_{n+1}, y_{n+2} = j) / P(η₁, …, η_{n+1}) = ‖z^j(u, w(n + 1))‖`,
with `u = c(η(n + 1), n + 1)` and `w(n + 1)` the conditional distribution of `x_{n+1}` given
`η(n + 1)`, both probabilities computed from the joint law of states and outputs. -/
theorem norm_predictive {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) (c : ControlLaw Obs r) (hc : Admissible M c) (n : ℕ)
    (η : Fin (n + 1) → Obs) (hn : n + 2 ≤ M.N) (hη : obsProb M c (n + 1) η ≠ 0) (j : Obs) :
    obsProb M c (n + 2) (Fin.snoc η j) / obsProb M c (n + 1) η =
      l1 (zvec M (c (n + 1) η) (n + 1) (condState M c n η) j) := by sorry

end AstromPOMDP.Reduction

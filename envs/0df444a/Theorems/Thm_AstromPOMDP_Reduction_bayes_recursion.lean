-- Prove2me | Theorems.Thm_AstromPOMDP_Reduction_bayes_recursion
-- name    : AstromPOMDP.Reduction.bayes_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:43:24.624835+00:00
-- url     : https://prove2.me/theorems/34355904-a614-41bb-8657-2c1a544148bf
-- title:
--   (3.20)–(3.25), p. 183 — the conditional state distributions obey w(t + 1) = z^j(u, w(t))/‖z^j(u, w(t))‖
-- statement:
--   Let $c$ be an admissible control law and $u(t)=c(\eta(t),t)$. For outputs $\eta(t+1)=(\eta_1,\dots,\eta_{t+1})$ of positive probability, with $t\ge1$ and $t+1\le N$, write $w(t)$ and $w(t+1)$ for the conditional distributions of $x_t$ given $\eta(t)$ and of $x_{t+1}$ given $\eta(t+1)$, computed from the joint law of states and outputs. Then, with $j=\eta_{t+1}$,
--   $$
--   w(t+1)=\frac{z^j(u(t),w(t))}{\|z^j(u(t),w(t))\|},\qquad z^j(u,w)_i=\sum_s q_{ij}\,p_{si}(u,t+1)\,w_s .
--   $$
--   Initially, if $P(y_1=\eta_1)>0$, then $w_i(1)=p^1_i q_{i\eta_1}/\sum_s p^1_s q_{s\eta_1}$.
--
--   This is Bayes' rule for the hidden state: the conditional distribution is updated from the previous one and the new output alone, without the earlier outputs.
-- source:
--   Åström, Optimal Control of Markov Processes with Incomplete State Information, J. Math. Anal. Appl. 10(1):174–205 (1965), DOI 10.1016/0022-247X(65)90154-X, p. 183, §III.B, (3.20)–(3.25)

import Mathlib
import Definitions.Def_AstromPOMDP_Reduction_Belief

namespace AstromPOMDP.Reduction

/-- Åström (1965), J. Math. Anal. Appl. 10:174–205, §III.B, (3.20)–(3.25), p. 183: the recursive
equation for the conditional state distributions. For an admissible control law `c` and outputs
`η = (η₁, …, η_{n+2})` of positive probability, with `n + 2 ≤ N`, the conditional distribution of
`x_{n+2}` given `η(n + 2)`, computed from the joint law of states and outputs, is
`z^j(u, w(n + 1)) / ‖z^j(u, w(n + 1))‖` with `j = η_{n+2}`, `u = c(η(n + 1), n + 1)` and
`w(n + 1)` the conditional distribution of `x_{n+1}` given `η(n + 1)`. Initially, the conditional
distribution of `x₁` given `y₁ = η₁` is `w_i(1) = p₁(i) q_{iη₁} / Σ_s p₁(s) q_{sη₁}`.

**Formalization Note.** The second conjunct is the time-1 case of the same computation (Bayes'
rule for the first output), needed because the law of `x₁` is the model's datum. -/
theorem bayes_recursion {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) (c : ControlLaw Obs r) (hc : Admissible M c) :
    (∀ (n : ℕ) (η : Fin (n + 2) → Obs), n + 2 ≤ M.N → obsProb M c (n + 2) η ≠ 0 →
      condState M c (n + 1) η =
        bayesNext M (c (n + 1) (Fin.init η)) (n + 1) (condState M c n (Fin.init η))
          (η (Fin.last (n + 1)))) ∧
    (∀ η : Fin 1 → Obs, obsProb M c 1 η ≠ 0 → condState M c 0 η = bayes1 M (η 0)) := by sorry

end AstromPOMDP.Reduction

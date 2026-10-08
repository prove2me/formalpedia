-- Prove2me | Theorems.Thm_FixpNash_Bubelis_aux3_uniform
-- name    : FixpNash.Bubelis.aux3_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:23.517998+00:00
-- url     : https://prove2.me/theorems/e10f7658-dbc5-4fee-add3-eab50f9c3ada
-- title:
--   Proof of Lemma 7, p. 26 — if $\alpha \ne 0$, every Nash equilibrium of $G_f$ has $x_3(j) = 1/(m+1)$
-- statement:
--   Let $f(x) = c_0 x^m + \dots + c_m$ be a real polynomial with $f(0) \le 0$ and $f(1) \ge 0$ which has a unique root $\alpha$ in $[0,1]$, and let $G_f$ be the gadget of Lemma 7. Suppose $\alpha \neq 0$. Then in every mixed Nash equilibrium $x = (x_1, x_2, x_3)$ of $G_f$ the auxiliary player 3 plays the uniform strategy:
--   $$
--   x_3(j) = \frac{1}{m+1}, \qquad j = 0, \dots, m .
--   $$
--
--   Together with the strategies of players 1 and 2 forced earlier in the proof, this determines the whole equilibrium, which is the uniqueness half of Lemma 7.
--
--   **Formalization Note** The root $\alpha$ is a named parameter with the hypothesis $0 \le \alpha \le 1$, $f(\alpha) = 0$, and $\beta = \alpha$ for every root $\beta \in [0,1]$ of $f$.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), proof of Lemma 7, p. 26

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_FixpNash_Bubelis_Gadget

namespace FixpNash.Bubelis

/-- Proof of Lemma 7, p. 26: let `f` satisfy `f(0) ≤ 0`, `f(1) ≥ 0` and have the unique root `α`
in `[0, 1]`. If `α ≠ 0`, then in every Nash equilibrium `x` of the gadget `G_f` player 3 plays
the uniform strategy `x₃(j) = 1/(m + 1)`, `j = 0, …, m`. -/
theorem aux3_uniform {m : ℕ} (c : Fin (m + 1) → ℝ)
    (hf0 : poly c 0 ≤ 0) (hf1 : 0 ≤ poly c 1) (α : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1 ∧ poly c α = 0 ∧
      ∀ β : ℝ, 0 ≤ β → β ≤ 1 → poly c β = 0 → β = α)
    (hα0 : α ≠ 0) (x : ∀ p, Strat m p → ℝ) (hx : AGT.IsMixedNash (gadget c) x)
    (j : Fin (m + 1)) :
    x .aux3 j = 1 / ((m : ℝ) + 1) := by sorry

end FixpNash.Bubelis

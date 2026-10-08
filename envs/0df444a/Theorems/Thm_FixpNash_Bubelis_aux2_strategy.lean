-- Prove2me | Theorems.Thm_FixpNash_Bubelis_aux2_strategy
-- name    : FixpNash.Bubelis.aux2_strategy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:22.498902+00:00
-- url     : https://prove2.me/theorems/9745fe49-f0ce-469f-8f96-db3605d04f66
-- title:
--   Proof of Lemma 7, p. 26 — in every Nash equilibrium of $G_f$, $x_2(j) = \xi^{m-j}/\sum_{i=0}^m \xi^i$ with $\xi = x_1(0)$
-- statement:
--   Let $G_f$ be the gadget of Lemma 7 for coefficients $c_0, \dots, c_m$ (no hypothesis on $f$ is needed), let $x = (x_1, x_2, x_3)$ be a mixed Nash equilibrium of $G_f$, and let $\xi = x_1(0)$ be the probability the primary player puts on its strategy $0$. Then for every $j = 0, \dots, m$,
--   $$
--   x_2(j) = \frac{\xi^{m-j}}{\sum_{i=0}^{m} \xi^{i}},
--   $$
--   where $\xi^0 = 1$ for all $\xi$, including $\xi = 0$.
--
--   The strategy of player 2 is thus determined by that of the primary player; this is how the gadget turns the probability $\xi$ into the values of the polynomial $f$.
--
--   **Formalization Note** The exponent $m - j$ is natural-number subtraction, exact since $j \le m$; Lean's convention $0^0 = 1$ is the paper's. The denominator is at least $1$ since $\xi \ge 0$. The root hypotheses of Lemma 7 are not needed and are omitted.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), proof of Lemma 7, p. 26

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_FixpNash_Bubelis_Gadget

namespace FixpNash.Bubelis

open Finset

/-- Proof of Lemma 7, p. 26: in every Nash equilibrium `x` of the gadget `G_f`, writing
`ξ = x₁(0)`, player 2 plays `x₂(j) = ξ^(m-j) / ∑_{i=0}^m ξ^i` for every `j = 0, …, m`
(with `ξ^0 = 1`, also for `ξ = 0`). -/
theorem aux2_strategy {m : ℕ} (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hx : AGT.IsMixedNash (gadget c) x) (j : Fin (m + 1)) :
    x .aux2 j = x .primary 0 ^ (m - (j : ℕ)) / ∑ i ∈ range (m + 1), x .primary 0 ^ i := by sorry

end FixpNash.Bubelis

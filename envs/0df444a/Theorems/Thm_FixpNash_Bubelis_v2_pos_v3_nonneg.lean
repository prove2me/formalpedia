-- Prove2me | Theorems.Thm_FixpNash_Bubelis_v2_pos_v3_nonneg
-- name    : FixpNash.Bubelis.v2_pos_v3_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:24.753634+00:00
-- url     : https://prove2.me/theorems/121a7e9f-b981-4d7a-8213-1d246069c6f8
-- title:
--   Proof of Lemma 7, p. 26 — in every Nash equilibrium of $G_f$, $v_2 > 0$ and $v_3 \ge 0$
-- statement:
--   Let $G_f$ be the gadget of Lemma 7 for coefficients $c_0, \dots, c_m$ (no hypothesis on $f$ is needed), and let $x = (x_1, x_2, x_3)$ be a mixed Nash equilibrium of $G_f$. Let $v_2$ and $v_3$ be the expected payoffs of the auxiliary players 2 and 3 in $x$. Then
--   $$
--   v_2 > 0 \qquad\text{and}\qquad v_3 \ge 0 .
--   $$
--
--   These two signs are what the rest of the proof of Lemma 7 uses to force the strategy of player 2.
--
--   **Formalization Note** $v_2$, $v_3$ are `AGT.expectedPayoff (gadget c) x` at `aux2`, `aux3`; the Nash equilibrium is `AGT.IsMixedNash`. The root hypotheses of Lemma 7 are not needed and are omitted.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), proof of Lemma 7, p. 26

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_FixpNash_Bubelis_Gadget

namespace FixpNash.Bubelis

/-- Proof of Lemma 7, p. 26: in every Nash equilibrium `x` of the gadget `G_f`, the equilibrium
payoff `v₂` of player 2 is positive and the equilibrium payoff `v₃` of player 3 is nonnegative. -/
theorem v2_pos_v3_nonneg {m : ℕ} (c : Fin (m + 1) → ℝ) (x : ∀ p, Strat m p → ℝ)
    (hx : AGT.IsMixedNash (gadget c) x) :
    0 < AGT.expectedPayoff (gadget c) x .aux2 ∧ 0 ≤ AGT.expectedPayoff (gadget c) x .aux3 := by sorry

end FixpNash.Bubelis

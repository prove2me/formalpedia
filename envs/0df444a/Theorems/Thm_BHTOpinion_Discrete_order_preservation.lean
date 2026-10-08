-- Prove2me | Theorems.Thm_BHTOpinion_Discrete_order_preservation
-- name    : BHTOpinion.Discrete.order_preservation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:42.947078+00:00
-- url     : https://prove2.me/theorems/ca64ddfd-618e-4078-b85b-9ca691d1b719
-- title:
--   Order preservation: for a proper solution, x_j(t) ≤ x_i(t) implies x_j(t′) ≤ x_i(t′) for all t′ ≥ t
-- statement:
--   Let $x$ be a proper solution of the integral equation (2.1) for $n$ agents (see the definition file). If $x_i(t)\ge x_j(t)$ holds for some time $t\ge0$, then this inequality holds for all subsequent times:
--
--   $$x_i(t)\ge x_j(t)\quad\Longrightarrow\quad x_i(t')\ge x_j(t')\ \text{ for every } t'\ge t .$$
--
--   The paper derives this from condition (c) (agents that meet stay together) and from the continuity of proper solutions. It is what justifies the paper's convention that the components of a proper initial condition are sorted: sorted initial opinions stay sorted for all time.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, SIAM J. Control Optim. 48 (2010), Section 2.1, p. 5218, paragraph after Theorem 1

import Mathlib
import Definitions.Def_BHTOpinion_Discrete_Model

open Filter Topology

namespace BHTOpinion.Discrete

theorem order_preservation {n : ℕ} (x : ℝ → Fin n → ℝ) (hx : IsProperSolution x)
    (i j : Fin n) (t t' : ℝ) (ht : 0 ≤ t) (htt' : t ≤ t') (hij : x t j ≤ x t i) :
    x t' j ≤ x t' i := by sorry

end BHTOpinion.Discrete

-- Prove2me | Theorems.Thm_BitcoinOligopoly_EoS_proposition_1
-- name    : BitcoinOligopoly.EoS.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:14.642405+00:00
-- url     : https://prove2.me/theorems/85b3f0df-552f-468c-87aa-7d5d57f28480
-- title:
--   Proposition 1 — investment and cost ordering
-- statement:
--   Let $q$ be a pure Nash equilibrium of the economies-of-scale model, with $n\ge2$, $\alpha\ge1$, and positive unit costs. If miners $i$ and $j$ both participate and $q_i\ge q_j>0$, then
--
--   $$
--   c_i\le c_j,\qquad c_i=c_j\iff q_i=q_j.
--   $$
--
--   Thus a larger positive equilibrium investment identifies a weakly lower unit cost, with equal costs exactly when the investments are equal.
-- source:
--   Arnosti & Weinberg, Bitcoin: A Natural Oligopoly, arXiv:1811.08572v1, p. 10 (PDF 11), Proposition 1

import Mathlib
import Definitions.Def_BitcoinOligopoly_EoS_Model

namespace BitcoinOligopoly.EoS

/-- Proposition 1, p. 10 (PDF 11): investment order reverses cost order. -/
theorem proposition_1 {n : ℕ} (P : Params n) (hP : P.Standing) (q : Fin n → ℝ)
    (hq : IsEquilibrium P q) (i j : Fin n) (hij : q j ≤ q i) (hj : 0 < q j) :
    P.c i ≤ P.c j ∧ (P.c i = P.c j ↔ q i = q j) := by sorry

end BitcoinOligopoly.EoS

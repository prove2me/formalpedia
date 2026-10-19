-- Prove2me | Theorems.Thm_BitcoinOligopoly_EoS_lemma_3
-- name    : BitcoinOligopoly.EoS.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:16.707222+00:00
-- url     : https://prove2.me/theorems/644eb9e6-60ae-4fc3-9d39-0a78546fefa5
-- title:
--   Lemma 3 — equilibrium first-order conditions
-- statement:
--   Let $q$ be a pure Nash equilibrium of the economies-of-scale model with $n\ge2$, $\alpha\ge1$, and positive unit costs $c_i$. Then every miner $i$ satisfies
--
--   $$
--   c_iq_i=\alpha x_i(q)(1-x_i(q)),\qquad
--   c_i\ge\frac{\alpha q_i^{\alpha-1}(1-x_i(q))}{\sum_jq_j^\alpha}.
--   $$
--
--   The equality applies also to nonparticipants, where both sides vanish. The inequality retains the separate boundary condition at $q_i=0$ and supplies the first-order information used in later results.
--
--   **Formalization Note** The standing assumptions and nonnegative strategy space come from §§3–4. `Real.rpow` makes $0^0=1$, so the inequality at $q_i=0$ remains meaningful when $\alpha=1$.
-- source:
--   Arnosti & Weinberg, Bitcoin: A Natural Oligopoly, arXiv:1811.08572v1, p. 9 (PDF 10), Lemma 3 and equation (6)

import Mathlib
import Definitions.Def_BitcoinOligopoly_EoS_Model

namespace BitcoinOligopoly.EoS

/-- Lemma 3, p. 9 (PDF 10), including equation (6) and the boundary inequality. -/
theorem lemma_3 {n : ℕ} (P : Params n) (hP : P.Standing) (q : Fin n → ℝ)
    (hq : IsEquilibrium P q) :
    (∀ i, P.c i * q i = P.α * share P q i * (1 - share P q i)) ∧
    (∀ i, P.α * q i ^ (P.α - 1) * (1 - share P q i) /
      (∑ j, q j ^ P.α) ≤ P.c i) := by sorry

end BitcoinOligopoly.EoS

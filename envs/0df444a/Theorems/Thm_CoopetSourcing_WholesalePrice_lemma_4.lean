-- Prove2me | Theorems.Thm_CoopetSourcing_WholesalePrice_lemma_4
-- name    : CoopetSourcing.WholesalePrice.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:10.222978+00:00
-- url     : https://prove2.me/theorems/253c30aa-9222-4a0a-b7ec-22b3b9d1e622
-- title:
--   Lemma 4, p. 18 — for t ≥ t̲ = 28(4 + 5√2)/1105, the separating profit Πs_I(wI) is increasing on the separating region
-- statement:
--   Let $t$ be the size of the demand shock and $w_A$ the outside price, with $\underline t := 28(4 + 5\sqrt2)/1105 \approx 0.2805 \le t$ and $126(17 - 3\sqrt{34})/(570\sqrt{34} - 15829) < w_A < 1/2 - 5t/7$. Let $\Pi^s_I(w_I) = \tfrac12\Pi^s_I(w_I|H) + \tfrac12\Pi^s_I(w_I|L)$ be the VI's expected profit at the separating quantities of Lemma 1. Then $\Pi^s_I$ is strictly increasing on the separating region of Lemma 1,
--   $$0 \le w_I < \frac{1 + t}{2} - \frac{\sqrt6\,(7 + 10t - 14w_A)}{35}.$$
--
--   Consequently, whenever the separating equilibrium is the outcome, the VI prices at the top of the separating range, $w_I^* = \bar w_{sep/pool}$.
--
--   **Formalization Note** The page says "monotonically increasing" without naming the domain; the proof says "in the entire range" of the separating equilibrium, which is Lemma 1's existence region, used here. The proof shows strict increase, which is stated. The bounds on $w_A$ are the paper's standing assumptions (pp. 10, 18).
-- source:
--   Jung & Kouvelis, “On Co-opetitive Supply Partnerships with End-Product Rivals”, SSRN preprint 3555184 (PDF of 2020-03-06), p. 18, Lemma 4; proof on Online Supplement p. S5

import Mathlib
import Definitions.Def_CoopetSourcing_WholesalePrice_Model

namespace CoopetSourcing.WholesalePrice

theorem lemma_4 (t wA : ℝ) (h : Standing t wA) : StrictMonoOn (profitSep t wA) (Set.Ico 0 (sepBound t wA)) := by sorry

end CoopetSourcing.WholesalePrice

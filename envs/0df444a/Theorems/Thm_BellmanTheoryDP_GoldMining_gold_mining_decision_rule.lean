-- Prove2me | Theorems.Thm_BellmanTheoryDP_GoldMining_gold_mining_decision_rule
-- name    : BellmanTheoryDP.GoldMining.gold_mining_decision_rule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T09:53:55.231748+00:00
-- url     : https://prove2.me/theorems/d6cdc945-f17b-4f91-8fb7-d37a976896c5
-- title:
--   Eq. (8.3), corrected — Bellman's index rule for the gold-mining problem, with $(1-p)$, $(1-q)$ in place of the misprinted $(1-r)$, $(1-s)$
-- statement:
--   In Bellman's gold-mining problem, let $0 < p, q, r, s < 1$ and $x, y \ge 0$, let $f$ be the optimal return, and let
--   $$V_A = p\,\big[r x + f((1-r)x,\ y)\big], \qquad V_B = q\,\big[s y + f(x,\ (1-s)y)\big]$$
--   be the two branches of the functional equation (8.2) (use Anaconda first, resp. Bonanza first, then continue optimally). Then
--
--   1. if $\dfrac{p r x}{1-p} > \dfrac{q s y}{1-q}$, then $V_A > V_B$ (choose $A$);
--   2. if $\dfrac{p r x}{1-p} < \dfrac{q s y}{1-q}$, then $V_A < V_B$ (choose $B$);
--   3. if $\dfrac{p r x}{1-p} = \dfrac{q s y}{1-q}$, then $V_A = V_B$ (choose either).
--
--   The optimal decision is therefore determined by comparing, for each mine, the immediate expected gain $p r x$ (resp. $q s y$) with the immediate expected loss $1 - p$ (resp. $1 - q$), the probability of destroying the machine.
--
--   The paper prints $(1-r)$, $(1-s)$ in the denominators; this is a misprint, and the statement uses $(1-p)$, $(1-q)$, which is the rule the paper describes in words ("immediate expected gain over immediate expected loss"). As printed the rule is false: for $p = 1/2$, $r = 0.9$, $q = 0.9$, $s = 0.1$, $x = 1$, $y = 2$ the printed indices are $4.5 > 0.2$, but $V_A \approx 0.924 < V_B \approx 1.055$.
--
--   **Formalization Note** The parameter ranges are left implicit in the paper; the statement takes $0 < p, q, r, s < 1$ (so the divisions by $1-p$ and $1-q$ are by positive numbers) and $x, y \ge 0$, amounts which may be zero. Parts 1 and 2 are strict preferences.
-- source:
--   Bellman, The theory of dynamic programming, Bull. Amer. Math. Soc. 60 (1954), p. 509, Eq. (8.3) (with (1−p), (1−q) in place of the misprinted (1−r), (1−s))

import Mathlib
import Definitions.Def_BellmanTheoryDP_GoldMining_Model

namespace BellmanTheoryDP.GoldMining

/-- Bellman (1954), Eq. (8.3), with the printed denominators `(1 - r)`, `(1 - s)` corrected to
`(1 - p)`, `(1 - q)`: comparing the two branches of (8.2),
`V_A = p [r x + f((1-r) x, y)]` and `V_B = q [s y + f(x, (1-s) y)]`,
(a) if `p r x / (1 - p) > q s y / (1 - q)` then `V_A > V_B` (choose A);
(b) if `p r x / (1 - p) < q s y / (1 - q)` then `V_A < V_B` (choose B);
(c) if `p r x / (1 - p) = q s y / (1 - q)` then `V_A = V_B` (choose either). -/
theorem gold_mining_decision_rule (p q r s x y : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (q * s * y / (1 - q) < p * r * x / (1 - p) →
        q * (s * y + optimalReturn p q r s x ((1 - s) * y)) <
          p * (r * x + optimalReturn p q r s ((1 - r) * x) y)) ∧
    (p * r * x / (1 - p) < q * s * y / (1 - q) →
        p * (r * x + optimalReturn p q r s ((1 - r) * x) y) <
          q * (s * y + optimalReturn p q r s x ((1 - s) * y))) ∧
    (p * r * x / (1 - p) = q * s * y / (1 - q) →
        p * (r * x + optimalReturn p q r s ((1 - r) * x) y) =
          q * (s * y + optimalReturn p q r s x ((1 - s) * y))) := by sorry

end BellmanTheoryDP.GoldMining

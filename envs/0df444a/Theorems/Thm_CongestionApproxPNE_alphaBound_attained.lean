-- Prove2me | Theorems.Thm_CongestionApproxPNE_alphaBound_attained
-- name    : CongestionApproxPNE.alphaBound_attained
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:34.146357+00:00
-- url     : https://prove2.me/theorems/0c8d491a-6e08-451c-b7b8-33d75ca64ba8
-- title:
--   Proof of Theorem 1 — the supremum (3) is attained when $\alpha(d)>1$
-- statement:
--   Let $d\ge 2$ and suppose $\alpha(d)>1$. Then the supremum (3) is attained at a point of the gadget family with a positive light weight: there are $n\in\mathbb N$, $k\in\{1,\dots,d\}$, $w\in(0,1]$ and $\beta\in[0,1]$ with $(nw)^k+\beta(1+w)^d>0$ and
--
--   $$
--   \min\left\{\frac{1+n\beta(1+w)^d}{(1+nw)^k+n\beta},\ \frac{(1+w)^k+\beta w^d}{(nw)^k+\beta(1+w)^d}\right\}=\alpha(d).
--   $$
--
--   Together with the nonexistence of $\alpha$-PNE in a single gadget below both ratios, this shows that one game of degree $d$ has no $\alpha$-PNE for every $\alpha<\alpha(d)$ at once.
--
--   Differences from the source:
--   - reading: "Maximizing these ratios over all games in the family, yields the lower bound" (a supremum, with attainment left implicit) → the supremum α(d) is attained at a tuple with w > 0 whenever α(d) > 1; reason: the page's "maximizing" is read as a maximum; this is what Theorem 1's stronger reading (one game for every α < α(d)) needs; it is true (for each n the min extends continuously to the compact parameter box, and a min ≥ 1 + δ forces nw ≤ 2^d + 1 and so only finitely many n)
--   - encoding: α(d) = sup over n ∈ ℕ, k ∈ {1,…,d}, w, β ∈ [0, 1] of the min of the two ratios (3) → sSup of the min over those points at which the second denominator (nw)^k + β(1+w)^d is positive; reason: (3) is undefined where that denominator is 0 (nw = 0, β = 0); with the convention 1/0 = +∞ those points give the value 1, already in the set, so the supremum is unchanged; the set is nonempty and bounded by 2^d
-- source:
--   Christodoulou et al., Existence and Complexity of Approximate Equilibria in Weighted Congestion Games, arXiv:2002.07466v3, proof of Theorem 1, p.5 (PDF p.6), "Maximizing these ratios over all games in the family, yields the lower bound in the statement of the theorem"

import Mathlib
import Definitions.Def_CongestionApproxPNE_ratioOne
import Definitions.Def_CongestionApproxPNE_ratioTwo
import Definitions.Def_CongestionApproxPNE_alphaBound

set_option autoImplicit false

namespace CongestionApproxPNE

/-- **The supremum (3) is attained, at a positive light weight, whenever `α(d) > 1`.**
Christodoulou, Gairing, Giannakopoulos, Poças, Waldmann, *Existence and Complexity of Approximate
Equilibria in Weighted Congestion Games*, arXiv:2002.07466v3, proof of Theorem 1, p.5: "Maximizing these ratios over all games in the family, yields the
lower bound in the statement of the theorem," (the attainment is implicit there; it is what makes a
single game work for every `α < α(d)`).

For `d ≥ 2` with `α(d) > 1` there are `n ∈ ℕ`, `k ∈ {1,…,d}`, `w ∈ (0,1]`, `β ∈ [0,1]` with
`(nw)^k + β(1+w)^d > 0` and
`min{(1 + nβ(1+w)^d)/((1+nw)^k + nβ), ((1+w)^k + βw^d)/((nw)^k + β(1+w)^d)} = α(d)`.

**Formalization Note** Not a printed statement: the step that turns the paper's supremum into one
game (reading "one game, every `α < α(d)`" of Theorem 1). `w > 0` is needed for the parameter to
be a game weight. -/
theorem alphaBound_attained (d : ℕ) (hd : 2 ≤ d) (h1 : 1 < alphaBound d) :
    ∃ (n k : ℕ) (w β : ℝ), 1 ≤ k ∧ k ≤ d ∧ 0 < w ∧ w ≤ 1 ∧ 0 ≤ β ∧ β ≤ 1 ∧
      0 < ((n : ℝ) * w) ^ k + β * (1 + w) ^ d ∧
      min (ratioOne d n k w β) (ratioTwo d n k w β) = alphaBound d := by sorry

end CongestionApproxPNE

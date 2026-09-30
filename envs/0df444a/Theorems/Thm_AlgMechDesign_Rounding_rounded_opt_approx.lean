-- Prove2me | Theorems.Thm_AlgMechDesign_Rounding_rounded_opt_approx
-- name    : AlgMechDesign.Rounding.rounded_opt_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T22:08:28.466988+00:00
-- url     : https://prove2.me/theorems/c40e9d54-4def-49bd-8725-2fa690cb5eff
-- title:
--   §5.6 — the solution of the rounded problem is a $(1+\varepsilon)$-approximation
-- statement:
--   Let $0 < a < b$ and $\varepsilon > 0$, and let the rounding step satisfy $0 < \delta \le \varepsilon a$. Let $t$ be a type vector with $a \le t^i_j \le b$ for all $i,j$, and let $\hat t$ be $t$ rounded up entrywise to integer multiples of $\delta$. If an allocation $x$ is optimal for the rounded times, i.e. $g(x,\hat t) \le g(y,\hat t)$ for every allocation $y$, then $x$ is a $(1+\varepsilon)$-approximation for the original times:
--   $$g(x,t) \le (1+\varepsilon)\, g(y,t) \quad\text{for every allocation } y.$$
--
--   This is the approximation guarantee of the Horowitz–Sahni rounding scheme, and the reason the rounding mechanism's outcome is near-optimal.
--
--   **Formalization Note** The paper leaves $\delta$ as "a parameter chosen as a function of $a$ and $\varepsilon$"; the statement holds for every $\delta \in (0, \varepsilon a]$, which covers the intended choice $\delta = \varepsilon a$. The upper bound $b$ is not used; it is kept because it is part of the bounded problem.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 192, §5.6, paragraph after Definition 33, last sentence (citing Horowitz and Sahni 1976)

import Mathlib
import Definitions.Def_AlgMechDesign_Rounding_Model

namespace AlgMechDesign.Rounding

/-- §5.6, p. 192 (paragraph after Def. 33, last sentence): with times in `[a, b]`, `a > 0`, and
a rounding step `0 < δ ≤ ε a`, every allocation that is optimal for the rounded times `t̂` is a
`(1 + ε)`-approximation of the optimal make-span for the original times `t`. -/
theorem rounded_opt_approx {n k : ℕ} [NeZero n] (a b ε δ : ℝ) (ha : 0 < a) (hab : a < b)
    (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ ≤ ε * a)
    (t : Fin n → Fin k → ℝ) (ht : IsBoundedType a b t) (x : Fin k → Fin n)
    (hx : ∀ y : Fin k → Fin n, makespan (roundType δ t) x ≤ makespan (roundType δ t) y) :
    ∀ y : Fin k → Fin n, makespan t x ≤ (1 + ε) * makespan t y := by sorry

end AlgMechDesign.Rounding

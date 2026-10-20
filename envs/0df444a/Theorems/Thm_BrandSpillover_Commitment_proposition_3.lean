-- Prove2me | Theorems.Thm_BrandSpillover_Commitment_proposition_3
-- name    : BrandSpillover.Commitment.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:59.303266+00:00
-- url     : https://prove2.me/theorems/bf2fdb7e-649b-4002-9cac-883629142bfb
-- title:
--   Proposition 3, p. 17 — when the CM induces (O, O) and when (O, I) (T1 and the c = c^oo_1 boundary corrected)
-- statement:
--   Assume the standing assumptions and a spillover level $a \in [0,1]$. Let $c^{oi}$, $c^{oo}_1$, $T_1$, $T_2$, $T_3$ be as in the model, where
--
--   $$T_1 = \theta - \tfrac12 - \tfrac12\sqrt{(2\theta-1)^2 - 4a^2(1-\theta)^2 - 8a + 18a\theta - 10a\theta^2},$$
--   $$T_{2,3} = \theta - \tfrac12 + \tfrac32 a - \tfrac32 a\theta \mp \tfrac12\sqrt{10a^2(1-\theta)^2 + 2 - 8\theta(1-\theta) - 16a + 36a\theta - 20a\theta^2}.$$
--
--   Consider the conditions
--
--   1. $T_1 < c \le c^{oo}_1$ and $c < c^{oi}$;
--   2. $\max\{c^{oo}_1, T_2\} < c < \min\{c^{oi}, T_3\}$;
--   3. $c \ge c^{oi}$.
--
--   If one of them holds, the CM induces $(O,O)$: an equilibrium with structure $(O,O)$ exists and every equilibrium has structure $(O,O)$. Otherwise $(O,I)$ is an equilibrium structure.
--
--   This is the equilibrium sourcing structure: with $a = \alpha$ it describes the game without commitment, with $a = 0$ the game with commitment.
--
--   **Formalization Note** Two corrections to the printed statement. (a) The page prints $4\alpha^2(1+\theta)^2$ in $T_1$; setting the CM's profit difference to zero gives $4\alpha^2(1-\theta)^2$, which is used here. (b) The page's condition (i) reads $T_1 < c < \min\{c^{oi}, c^{oo}_1\}$, and (ii) requires $c > c^{oo}_1$, so the point $c = c^{oo}_1$ falls under "otherwise". There the CM's profit difference is given by the formula of condition (i) and can be strictly positive; for example at $\theta = 4/5$, $\alpha = 1/2$, $c = c^{oo}_1 = 3/20$ the $(O,O)$ profit exceeds the $(O,I)$ profit by $23/1200$. Condition (i) is therefore closed at $c = c^{oo}_1$. When a radicand is negative, `Real.sqrt` gives $0$; then condition (i) or (ii) is empty, matching the case in which the CM's profit difference has no real root.
-- source:
--   Wu, Zhang & Zhou, Brand Spillover as a Marketing Strategy, SSRN preprint 3891915 (June 2021), p. 17, Proposition 3 and the definitions of T1, T2, T3 (proof App. A, pp. 33–34)

import Mathlib
import Definitions.Def_BrandSpillover_Commitment_Model

namespace BrandSpillover.Commitment

/-- Proposition 3, p. 17, at spillover level `a ∈ [0, 1]`, with two corrections (see the item's
statement): `T1` has the factor `(1 − θ)²`, and condition (i) includes the boundary `c = c^oo_1`.
Under (i) `T1 < c ≤ c^oo_1`, `c < c^oi`, (ii) `max {c^oo_1, T2} < c < min {c^oi, T3}`, or
(iii) `c ≥ c^oi`, the CM induces `(O, O)` (and only `(O, O)`); otherwise `(O, I)` is an
equilibrium structure. -/
theorem proposition_3 (P : Params) (hP : P.Standing) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (((T1 P a < P.c ∧ P.c ≤ cOO1 P a ∧ P.c < cOI P) ∨
        (max (cOO1 P a) (T2 P a) < P.c ∧ P.c < min (cOI P) (T3 P a)) ∨ cOI P ≤ P.c) →
      (∃ w : ℝ × ℝ, IsEquilibrium P a .OO w) ∧
      ∀ (s : Structure) (w : ℝ × ℝ), IsEquilibrium P a s w → s = .OO) ∧
    (¬ ((T1 P a < P.c ∧ P.c ≤ cOO1 P a ∧ P.c < cOI P) ∨
        (max (cOO1 P a) (T2 P a) < P.c ∧ P.c < min (cOI P) (T3 P a)) ∨ cOI P ≤ P.c) →
      ∃ w : ℝ × ℝ, IsEquilibrium P a .OI w) := by sorry

end BrandSpillover.Commitment

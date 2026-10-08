-- Prove2me | Theorems.Thm_DoubleGreedyUSM_Fractional_eq4_eq5
-- name    : DoubleGreedyUSM.Fractional.eq4_eq5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:05:19.151978+00:00
-- url     : https://prove2.me/theorems/e09b7c13-8fd5-4022-9e9d-0d9901dda0d4
-- title:
--   Proof of Lemma A.2, Case 3, (4)–(5) — $F(x_i) - F(x_{i-1}) = a_i^2/(a_i+b_i)$ and $F(y_i) - F(y_{i-1}) = b_i^2/(a_i+b_i)$
-- statement:
--   Let $f : 2^{\mathcal N} \to \mathbb R$ be any set function with multilinear extension $F$, and run Algorithm 4 on $f$ in an order $u_1, \dots, u_n$. At an iteration $1 \le i \le n$ with
--   $$a_i = F(x_{i-1} + \{u_i\}) - F(x_{i-1}) \ge 0 \quad\text{and}\quad b_i = F(y_{i-1} - \{u_i\}) - F(y_{i-1}) > 0$$
--   (Case 3 of the proof of Lemma A.2), the two vectors change in value by
--   $$F(x_i) - F(x_{i-1}) = \frac{a_i^2}{a_i + b_i}, \qquad F(y_i) - F(y_{i-1}) = \frac{b_i^2}{a_i + b_i} .$$
--
--   These are the gains of the two solutions in the case where the algorithm splits coordinate $u_i$ strictly between the two moves; together with inequality (6) they give Lemma A.2 in that case.
--
--   **Formalization Note.** The identities only use that $F$ is affine in each coordinate, so no submodularity or nonnegativity of $f$ is assumed, and the order $l$ may be any list (a generalization of the page, where $l$ enumerates the ground set). The paper writes the middle expression with $F(x_{i-1} \vee \{u_i\})$; only the outer equalities (4) and (5) are stated.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, proof of Lemma A.2, Case 3, equalities (4) and (5) (PDF p. 10)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_DoubleGreedyUSM_Fractional_Algorithm4

namespace DoubleGreedyUSM.Fractional

/-- Proof of Lemma A.2, Case 3, equalities (4) and (5) (PDF p. 10): at an iteration `i` of
Algorithm 4 with `a_i ≥ 0` and `b_i > 0`,
`F(x_i) − F(x_{i−1}) = a_i² / (a_i + b_i)` and `F(y_i) − F(y_{i−1}) = b_i² / (a_i + b_i)`. -/
theorem eq4_eq5 {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (l : List X) (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ l.length)
    (ha : 0 ≤ aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega)))
    (hb : 0 < bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega))) :
    NonmonotoneSubmod.Shared.F f (state f l i).1 - NonmonotoneSubmod.Shared.F f (state f l (i - 1)).1
        = aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega)) ^ 2
          / (aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega))
              + bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega))) ∧
    NonmonotoneSubmod.Shared.F f (state f l i).2 - NonmonotoneSubmod.Shared.F f (state f l (i - 1)).2
        = bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega)) ^ 2
          / (aGain f (state f l (i - 1)).1 (l[i - 1]'(by omega))
              + bGain f (state f l (i - 1)).2 (l[i - 1]'(by omega))) := by sorry

end DoubleGreedyUSM.Fractional

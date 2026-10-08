-- Prove2me | Theorems.Thm_Disjunctive_MonoidalStrengthening_gmi_strictly_dominating_cuts_v2
-- name    : Disjunctive.MonoidalStrengthening.gmi_strictly_dominating_cuts_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:42.117986+00:00
-- url     : https://prove2.me/theorems/94b68679-ce37-42c7-9224-d10fc48e1bd0
-- title:
--   Theorem 11.26 — two strengthened GMI-type cuts $\alpha^+x\ge1$, $\alpha^-x\ge1$ for a 0-1 basic variable
-- statement:
--   This is Theorem 11.26 of Balas's *Disjunctive Programming*, the goal theorem of the mission: two refinements of the Gomory mixed-integer cut obtained by monoidal (Lopsided) strengthening of the split disjunction.
--
--   Let $y = a_0 - \sum_{j\in J} a_j x_j$ be the simplex-tableau row of a basic $0$-$1$ variable $y$, with $0 < a_0 < 1$, nonbasic variables $x \ge 0$, and $x_j \in \mathbb Z$ for $j\in J_1\subseteq J$. Define
--   $$
--   \alpha^+_j := \begin{cases}
--   \dfrac{1-a_j}{1-a_0}, & j \in J^+_1 := \{j\in J_1 : a_j > 1\},\\[6pt]
--   \min\Big\{\dfrac{a_j-\lfloor a_j\rfloor}{a_0},\ \dfrac{\lceil a_j\rceil - a_j}{1-a_0}\Big\}, & j \in \{j\in J_1 : a_0-1 \le a_j \le 1\},\\[6pt]
--   \max\Big\{\dfrac{a_j}{a_0},\ \dfrac{-a_j}{1-a_0}\Big\}, & \text{otherwise},
--   \end{cases}
--   $$
--   and symmetrically
--   $$
--   \alpha^-_j := \begin{cases}
--   \dfrac{a_j+1}{a_0}, & j \in J^-_1 := \{j\in J_1 : a_j < -1\},\\[6pt]
--   \min\Big\{\dfrac{a_j-\lfloor a_j\rfloor}{a_0},\ \dfrac{\lceil a_j\rceil - a_j}{1-a_0}\Big\}, & j \in \{j\in J_1 : -1 \le a_j \le a_0\},\\[6pt]
--   \max\Big\{\dfrac{a_j}{a_0},\ \dfrac{-a_j}{1-a_0}\Big\}, & \text{otherwise}.
--   \end{cases}
--   $$
--   Then every $x$ as above for which $y\in\{0,1\}$ satisfies both $\alpha^+x \ge 1$ and $\alpha^-x \ge 1$.
--
--   **Formalization Note.** The retired version assumed only that the real number $y = a_0-\sum_j a_jx_j$ satisfies $y\le 0 \lor y\ge 1$. It thus dropped that $y$ is an integer variable with the LP bounds $0\le y\le 1$. These bounds are the lower bounds $b_1 = a_0-1$ and $b_2 = -a_0$ of the two terms of the split disjunction, which the book's Lopsided-cut derivation (Theorem 11.23 with $k=2$, resp. $k=1$) uses: the negative coefficient $(1-a_j)/(1-a_0)$ on $J_1^+$ is valid only because $y\ge 0$, and $(a_j+1)/a_0$ on $J_1^-$ only because $y\le1$. The counterexample $a_0=\tfrac12$, $a=(\tfrac32)$, $x=(1)$ gives $y=-1$. The new hypothesis `hy` states $y\in\{0,1\}$, which is the same as $y$ integer with $0\le y\le1$. The piecewise definitions `AlphaPlus`/`AlphaMinus` are unchanged.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §11.9.1, p. 187, Theorem 11.26 (eqs. (11.55)-(11.56))

import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic

namespace Disjunctive.MonoidalStrengthening

/-- Theorem 11.26 (Balas, *Disjunctive Programming*, Springer 2018, §11.9.1, p. 187), the goal
theorem of the mission. Consider the simplex-tableau row `y = a_0 - Σ_j a_j x_j` of a basic
variable `y` that is a `0`-`1` variable (integer, with the bounds `0 ≤ y ≤ 1` of the LP
relaxation, which give the lower bounds `b_1 = a_0 - 1`, `b_2 = -a_0` of the two terms of the
split disjunction `y ≤ 0 ∨ y ≥ 1` used by the book's Lopsided-cut derivation), with
`0 < a_0 < 1`, the nonbasic variables `x ≥ 0`, and `x_j` integer for `j ∈ J₁`. Then every such
`x` satisfies both `α⁺x ≥ 1` and `α⁻x ≥ 1`, with `α⁺`, `α⁻` given by (11.55)/(11.56).

Correction w.r.t. the retired version: the retired statement kept only the disjunction
`y ≤ 0 ∨ y ≥ 1` on the real number `y`, dropping integrality and the bounds `0 ≤ y ≤ 1` of the
basic variable; hypothesis `hy` now says `y ∈ {0,1}`. -/
theorem gmi_strictly_dominating_cuts_v2 {n : ℕ} (a0 : ℝ) (a : Fin n → ℝ) (J1 : Finset (Fin n))
    (ha0 : 0 < a0) (ha0' : a0 < 1)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (hy : a0 - ∑ j, a j * x j = 0 ∨ a0 - ∑ j, a j * x j = 1) :
    1 ≤ ∑ j, AlphaPlus a0 a J1 j * x j ∧ 1 ≤ ∑ j, AlphaMinus a0 a J1 j * x j := by sorry

end Disjunctive.MonoidalStrengthening

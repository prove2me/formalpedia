-- Prove2me | Theorems.Thm_Disjunctive_MonoidalStrengthening_gmi_strictly_dominating_cuts
-- name    : Disjunctive.MonoidalStrengthening.gmi_strictly_dominating_cuts
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:04:16.601719+00:00
-- url     : https://prove2.me/theorems/6e5b168b-754d-45e3-b4d9-225a9239ca70
-- title:
--   Theorem 11.26 — two cuts strictly dominating the Gomory mixed-integer cut
-- statement:
--   This is Theorem 11.26 of Balas's *Disjunctive Programming*, the goal theorem of this mission:
--   two refinements of the classical Gomory mixed-integer (GMI) cut, each strictly stronger than
--   the GMI cut on part of its domain (Corollary 11.27, not drafted this pass, gives the exact
--   domination condition).
--
--   Let $y := a_0 - \sum_j a_j x_j$ be a tableau row with $0 < a_0 < 1$, $x \ge 0$, and $x_j$
--   integer for $j \in J_1$. On either branch of the split disjunction $y \le 0 \lor y \ge 1$, both
--   $\alpha^+x \ge 1$ and $\alpha^-x \ge 1$ are valid, with
--
--   $$
--   \alpha^+_j := \begin{cases}
--   \dfrac{1-a_j}{1-a_0}, & j \in J^+_1 := \{j\in J_1 : a_j > 1\} \\[6pt]
--   \min\Big\{\dfrac{a_j-\lfloor a_j\rfloor}{a_0},\ \dfrac{\lceil a_j\rceil - a_j}{1-a_0}\Big\}, &
--   j \in J^{>}_1 := \{j\in J_1 : a_0-1 \le a_j \le 1\} \\[6pt]
--   \max\Big\{\dfrac{a_j}{a_0},\ \dfrac{-a_j}{1-a_0}\Big\}, & \text{otherwise}
--   \end{cases}
--   $$
--
--   and $\alpha^-_j$ symmetric (eq. (11.56)). Both refine the plain GMI coefficient $\max\{a_j/a_0,
--   -a_j/(1-a_0)\}$ (used uniformly by the ordinary GMI cut) with a sharper, piecewise formula on
--   a subset of $J_1$.
--
--   The book's proof derives $\alpha^+$ as a specialization of Theorem 11.23's Lopsided-cut
--   construction applied to the two-term disjunction (11.51) with $k=2$, checking the four ranges
--   of $a_j$ (relative to $0$, $a_0$, and $1$) case by case; the proof for $\alpha^-$ is symmetric.
--   Example 4 immediately following gives a fully worked six-variable instance whose GMI cut and
--   strengthened $\alpha^+$/$\alpha^-$ coefficients can be compared numerically.
--
--   **Formalization Note.** $\alpha^+$/$\alpha^-$ are formalized with the exact three-case
--   piecewise structure of (11.55)/(11.56), not collapsed into a uniform closed form — the
--   piecewise structure over $J^+_1$/$J^{>}_1$/otherwise (resp. $J^-_1$/$J^{<}_1$/otherwise) is
--   the theorem's actual content, since a single uniform formula would just reproduce the plain
--   GMI coefficient and could never be strictly stronger, which is exactly the trivializing
--   formalization `BRIEF.md` warns against. The hypothesis is stated directly as the split
--   disjunction on $y$'s value, rather than via a separately introduced `y` variable, since $y$'s
--   only role in the theorem is as shorthand for $a_0-\sum_j a_jx_j$.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 187, Theorem 11.26

import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic

namespace Disjunctive.MonoidalStrengthening

/-- Theorem 11.26 (Balas §11.9.1, p. 187), the goal theorem of this mission: for a tableau row
`y = a_0 - Σ_j a_j x_j` (`0 < a_0 < 1`), `x ≥ 0`, integer on `J₁`, both `α⁺x ≥ 1` and `α⁻x ≥ 1`
are valid cuts, i.e. hold for every `x` on either branch of the split disjunction `y ≤ 0 ∨ y ≥ 1`
from (11.50)/(11.51). -/
theorem gmi_strictly_dominating_cuts {n : ℕ} (a0 : ℝ) (a : Fin n → ℝ) (J1 : Finset (Fin n))
    (ha0 : 0 < a0) (ha0' : a0 < 1)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (hx_disj : a0 - ∑ j, a j * x j ≤ 0 ∨ 1 ≤ a0 - ∑ j, a j * x j) :
    1 ≤ ∑ j, AlphaPlus a0 a J1 j * x j ∧ 1 ≤ ∑ j, AlphaMinus a0 a J1 j * x j := by sorry

end Disjunctive.MonoidalStrengthening

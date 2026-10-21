-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_proposition_1
-- name    : BudgetAgg.NashChar.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:54.40598+00:00
-- url     : https://prove2.me/theorems/3f3bf389-b382-4a94-b48f-58d88f317789
-- title:
--   Proposition 1, p. 16 — with Leontief utilities, NASH is continuous
-- statement:
--   Let $g$ be the Nash product rule, i.e. a mechanism such that $g(P)$ maximizes $\prod_{i\in N}u_i$ over $\Delta^m$ for every profile $P$. Then $g$ is continuous as a map $(\Delta^m)^n\to\Delta^m$:
--   $$\forall P\ \forall\varepsilon>0\ \exists\delta>0\ \forall P':\ \|P-P'\|_1<\delta\ \Rightarrow\ \|g(P)-g(P')\|_1<\varepsilon.$$
--   Continuity is one of the three axioms of Theorem 3, so this is part of its existence half.
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`. "$q = NASH(P)$" is written as the predicate `IsNashOutcome P q` ($q\in\Delta^m$ maximizes the Nash product over $\Delta^m$); uniqueness of the maximizer is the separate item `nash_unique`. Continuity is `Continuous g` for the subtype topology, equivalent to the $\ell_1$ formulation of Definition 7 since all norms on $\mathbb R^{n\times m}$ are equivalent.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 16, Proposition 1 (proof pp. 31–33, App. E.1)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- Proposition 1, p. 16: every selection of Nash outcomes is continuous. -/
theorem proposition_1 {n m : ℕ} [NeZero n] [NeZero m]
    (g : Mechanism n m) (hg : ∀ P, IsNashOutcome P (g P).1) :
    Continuous g := by sorry

end BudgetAgg.NashChar

-- Prove2me | Theorems.Thm_ConvexOptimization_lmi_strict_alternative
-- name    : ConvexOptimization.lmi_strict_alternative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T16:04:14.176133+00:00
-- url     : https://prove2.me/theorems/fcf07c76-b0b1-4e64-9118-55d05d8f36a9
-- title:
--   Strict LMI theorem of alternatives
-- statement:
--   **Theorem of alternatives for a strict linear matrix inequality** — example 5.14 of Boyd & Vandenberghe.
--
--   Let $F_1,\dots,F_n, G$ be symmetric $k \times k$ real matrices and write $F(x) = G + \sum_{i=1}^{n} x_i F_i$. Then exactly one of the following two systems is feasible:
--
--   $$\exists x \in \mathbb{R}^n:\ F(x) \prec 0 \qquad\text{versus}\qquad \exists Z \in \mathbb{S}^{k}:\ Z \succeq 0,\ Z \ne 0,\ \operatorname{tr}(F_i Z) = 0 \ (i = 1,\dots,n),\ \operatorname{tr}(GZ) \ge 0 .$$
--
--   They are *strong* alternatives — never both feasible, never both infeasible.
--
--   The second system is a certificate that no $x$ makes $F(x)$ negative definite: a nonzero positive semidefinite $Z$ orthogonal to every $F_i$ and non-negatively paired with $G$. This is the semidefinite instance of the conic theorem of alternatives, obtained by taking $K$ to be the positive semidefinite cone, and it is the tool that reduces feasibility questions about LMIs — ubiquitous in control theory — to a search for such a $Z$.
--
--   **Formalization Note** $F(x) \prec 0$ is written `(-(G + ∑ i, x i • F i)).PosDef` and $Z \succeq 0$ as `Z.PosSemidef`; the trace pairings use `(F i * Z).trace`. The statement is an iff between the first system and the *negation* of the second. Source: B&V §5.9.4, example 5.14, pp. 270–271.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 270, §5.9.4 example 5.14 (feasibility of a strict linear matrix inequality: strong alternatives)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.lmi_strict_alternative {n nn : ℕ}
    (F : Fin n → Matrix (Fin nn) (Fin nn) ℝ) (hF : ∀ i, (F i).IsSymm)
    (G : Matrix (Fin nn) (Fin nn) ℝ) (hG : G.IsSymm) :
    (∃ x : Fin n → ℝ, (-(G + ∑ i, x i • F i)).PosDef) ↔
      ¬∃ Z : Matrix (Fin nn) (Fin nn) ℝ, Z.PosSemidef ∧ Z ≠ 0 ∧
        (∀ i, ((F i) * Z).trace = 0) ∧ 0 ≤ (G * Z).trace := by
  sorry

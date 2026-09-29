-- Prove2me | Theorems.Thm_ConvexOptimization_lmi_nonstrict_alternative
-- name    : ConvexOptimization.lmi_nonstrict_alternative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T16:04:30.976295+00:00
-- url     : https://prove2.me/theorems/e8d2c7d1-00a9-48b2-a248-84535e9162a3
-- title:
--   Nonstrict LMI theorem of alternatives
-- statement:
--   **Theorem of alternatives for a nonstrict linear matrix inequality** — exercise 5.44 of Boyd & Vandenberghe.
--
--   Let $F_1,\dots,F_n, G$ be symmetric $k \times k$ real matrices, write $F(x) = G + \sum_{i=1}^{n} x_i F_i$, and assume the constraint qualification
--
--   $$\sum_{i=1}^{n} v_i F_i \succeq 0 \;\Longrightarrow\; \sum_{i=1}^{n} v_i F_i = 0 \qquad (v \in \mathbb{R}^n).$$
--
--   Then exactly one of the following is feasible:
--
--   $$\exists x \in \mathbb{R}^n:\ F(x) \preceq 0 \qquad\text{versus}\qquad \exists Z \in \mathbb{S}^{k}:\ Z \succeq 0,\ \operatorname{tr}(F_i Z) = 0 \ (i = 1,\dots,n),\ \operatorname{tr}(GZ) > 0 .$$
--
--   Passing from the strict inequality $F(x) \prec 0$ to the nonstrict $F(x) \preceq 0$ moves the strictness to the other side — the certificate now has $\operatorname{tr}(GZ) > 0$ and drops the requirement $Z \ne 0$ — and it costs an extra hypothesis: without the displayed constraint qualification the two systems are only *weak* alternatives, and both can fail.
--
--   This is the version the proof of the S-procedure actually uses (B&V §B.4, where the cross-reference points at example 5.14, the strict variant, while the system being treated is nonstrict).
--
--   **Formalization Note** $F(x) \preceq 0$ is `(-(G + ∑ i, x i • F i)).PosSemidef`; the constraint qualification is the explicit hypothesis `hCQ`, part of the statement rather than a background assumption. Source: B&V §5.9.4, p. 271, exercise 5.44.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 271, 287, §5.9.4 (the nonstrict LMI case, stated with its extra assumption) and exercise 5.44, p. 287 (strong alternatives for nonstrict LMIs). The constraint qualification (sum_i v_i F_i >= 0 implies sum_i v_i F_i = 0) is part of the formalized statement. This nonstrict form, not the strict example 5.14, is the one the S-procedure proof in §B.4 applies

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.lmi_nonstrict_alternative {n nn : ℕ}
    (F : Fin n → Matrix (Fin nn) (Fin nn) ℝ) (hF : ∀ i, (F i).IsSymm)
    (G : Matrix (Fin nn) (Fin nn) ℝ) (hG : G.IsSymm)
    (hCQ : ∀ v : Fin n → ℝ, (∑ i, v i • F i).PosSemidef → ∑ i, v i • F i = 0) :
    (∃ x : Fin n → ℝ, (-(G + ∑ i, x i • F i)).PosSemidef) ↔
      ¬∃ Z : Matrix (Fin nn) (Fin nn) ℝ, Z.PosSemidef ∧
        (∀ i, ((F i) * Z).trace = 0) ∧ 0 < (G * Z).trace := by
  sorry

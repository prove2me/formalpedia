-- Prove2me | Theorems.Thm_ChanceDetEquiv_EModel_convex_29
-- name    : ChanceDetEquiv.EModel.convex_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:57:21.14752+00:00
-- url     : https://prove2.me/theorems/3e70f498-12ad-4c17-947d-ca98dd6cf4d0
-- title:
--   'E Model', pp. 28–29 — the feasible set of (29) is convex in (D, v)
-- statement:
--   Let every component $b_k$ be square integrable, and assume $\tfrac12<\alpha_i<1$ for each row $i$. The set of pairs $(D,v)$, with $D$ an $n\times m$ matrix and $v\in\mathbb R^m$, that satisfy the system (29),
--   $$\mu_i(D)-v_i\ge0,\qquad -K_{\alpha_i}^2\sigma_i^2(D)+K_{\alpha_i}^2\mu_i^2(D)+v_i^2\ge0,\qquad v_i\ge0\qquad(i=1,\dots,m),$$
--   is a convex subset of $\mathbb R^{n\times m}\times\mathbb R^m$.
--
--   The paper's justification: the first constraints are half spaces, and each quadratic constraint together with $v_i\ge0$ describes one nappe and the interior of an elliptic hyperboloid. This is what makes the deterministic equivalent (29) a convex programming problem.
--
--   **Formalization Note** Convexity is claimed for the set of pairs $(D,v)$ with $v_i\ge0$ included; the quadratic constraint alone (both nappes) does not describe a convex set. This item does not state convexity of the set of feasible $D$ of (18).
-- source:
--   Charnes and Cooper, Deterministic Equivalents for Optimizing and Satisficing under Chance Constraints, Oper. Res. 11 (1963), pp. 28–29, the paragraph after (30)

import Mathlib
import Definitions.Def_ChanceDetEquiv_EModel_Model

open MeasureTheory ProbabilityTheory Matrix

namespace ChanceDetEquiv.EModel

/-- **Convexity of (29)**, pp. 28–29: if every `b_k` is square integrable and
`½ < α_i < 1`, the set of pairs
`(D, v)` satisfying the constraint system (29) is convex in
`Matrix (Fin n) (Fin m) ℝ × (Fin m → ℝ)`. -/
theorem convex_29 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Ω → Fin m → ℝ)
    (hb : ∀ k, MemLp (fun ω => b ω k) 2 P) (α : Fin m → ℝ)
    (hα_lo : ∀ i, 1 / 2 < α i) (hα_hi : ∀ i, α i < 1) :
    Convex ℝ {p : Matrix (Fin n) (Fin m) ℝ × (Fin m → ℝ) | Sys29 P A b α p.1 p.2} := by sorry

end ChanceDetEquiv.EModel

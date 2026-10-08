-- Prove2me | Theorems.Thm_ConicQuadIPM_NTScaling_lemma_3_3_iv
-- name    : ConicQuadIPM.NTScaling.lemma_3_3_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:48.28062+00:00
-- url     : https://prove2.me/theorems/e4d1b7bb-48d3-46c2-9ee0-5e879eea1c15
-- title:
--   Lemma 3.3 iv), p. 12 — x ∈ K ⇔ x̄ ∈ K and x ∈ int(K) ⇔ x̄ ∈ int(K)
-- statement:
--   Let $K$ be one of $\mathbb R_+$, $K^q$, $K^r$ with matrix $Q$, let $\theta>0$, let $W$ be a scaling matrix ($W\succ0$, $WQW=Q$), and $\bar x = \theta W x$. Then
--   $$x\in K \iff \bar x\in K\qquad\text{and}\qquad x\in\operatorname{int}(K)\iff \bar x\in\operatorname{int}(K).$$
--
--   Scaling therefore maps the cone and its interior onto themselves, so the scaled iterates remain strictly feasible.
--
--   **Formalization Note** The statement is made for one cone block $K^i$, with the superscript $i$ dropped: $\Theta$ and $W$ are block diagonal (p. 11–12), so the per-block statement is the paper's statement block by block. Vectors are `Fin d → ℝ` with 0-based indices (the paper's $x_1$ is `coord x 0`); $\|x_{2:n}\|^2$ is `tailSq x 1`, a sum of squares (Euclidean, never Mathlib's sup norm); $x^Ts$ is `x ⬝ᵥ s`. The dimension conventions the paper leaves implicit ($d=1$ for $\mathbb R_+$, $d\ge 1$ for $K^q$, $d\ge2$ for $K^r$) are the hypothesis `WellFormedBlock kind d`. The interior $\operatorname{int}(K)$ is written with strict inequalities ($x_1 > \|x_{2:n}\|$; $2x_1x_2 > \|x_{3:n}\|^2$, $x_1,x_2>0$; $x_1>0$). The paper states iv) for the product cone $K = K^1\times\dots\times K^k$; since $\Theta$ and $W$ are block diagonal, it is equivalent to the per-block statement here.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003), DOI 10.1007/s10107-002-0349-3; authors' preprint of 18 Dec 2000, p. 12, Lemma 3.3 iv); proof pp. 37–38

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix

namespace ConicQuadIPM.NTScaling

/-- Lemma 3.3 iv), p. 12, for one cone block: `x ∈ K ⇔ x̄ ∈ K` and
`x ∈ int(K) ⇔ x̄ ∈ int(K)`, where `x̄ = θWx`. -/
theorem lemma_3_3_iv (kind : ConicQuadIPM.Complementarity.ConeKind) (d : ℕ) (hwf : WellFormedBlock kind d)
    (θ : ℝ) (hθ : 0 < θ) (W : Matrix (Fin d) (Fin d) ℝ) (hW : IsScaling kind d W)
    (x : Fin d → ℝ) :
    (ConicQuadIPM.Complementarity.inCone kind x ↔ ConicQuadIPM.Complementarity.inCone kind (xbar θ W x)) ∧
    (inConeInt kind x ↔ inConeInt kind (xbar θ W x)) := by sorry
end ConicQuadIPM.NTScaling

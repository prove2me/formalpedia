-- Prove2me | Theorems.Thm_EkelandVP_Constraints_theorem_3_1
-- name    : EkelandVP.Constraints.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T11:16:03.715177+00:00
-- url     : https://prove2.me/theorems/d8a9203c-86d6-4b97-8875-02f26bd04a7d
-- title:
--   Theorem 3.1, p. 330 — ε²-optimal feasible points satisfying the Lagrange multiplier rule up to ε
-- statement:
--   Let $V$ be a real Banach space with dual $V^*$, let $F:V\to\mathbb R$ be Fréchet-differentiable, and let $G_1,\dots,G_m:V\to\mathbb R$ be $C^1$ functions, $0\le p\le m$, defining the problem
--   $$\inf F(v)\quad\text{subject to}\quad G_i(v)=0\ (1\le i\le p),\qquad G_i(v)\ge0\ (p+1\le i\le m), \tag{3.1}$$
--   with feasible set $\mathcal C$ (3.2). Assume the regularity assumption (3.4): at every $v\in\mathcal C$ the derivatives $G_i'(v)$ of the saturated constraints $i\in I(v)$ are linearly independent. Assume $\mathcal C\neq\emptyset$ and that $F$ is bounded below on $\mathcal C$, $\inf_{v\in\mathcal C}F(v)>-\infty$ (3.5). Then for every $\varepsilon>0$ there exist a point $v_\varepsilon$ with
--   $$v_\varepsilon\in\mathcal C\qquad\text{and}\qquad F(v_\varepsilon)\le\inf_{v\in\mathcal C}F(v)+\varepsilon^2, \tag{3.6}$$
--   and real numbers $\lambda_1,\dots,\lambda_m$ with
--   $$\lambda_i\ge0\ \ (p+1\le i\le m),\qquad \lambda_i=0\ \text{ if } G_i(v_\varepsilon)\ne0,\qquad \Big\|F'(v_\varepsilon)-\sum_{i=1}^m\lambda_iG_i'(v_\varepsilon)\Big\|_*\le\varepsilon. \tag{3.7}$$
--
--   The problem (3.1) need have no solution in an infinite-dimensional space; the theorem asserts that nearly optimal points nevertheless satisfy the Karush–Kuhn–Tucker conditions up to an error $\varepsilon$ in the dual norm.
--
--   **Formalization Note.** The infimum over $\mathcal C$ is not formed in Lean: (3.5) is `BddBelow (F '' 𝒞)` and (3.6) is $F(v_\varepsilon)\le F(w)+\varepsilon^2$ for every $w\in\mathcal C$. Non-emptiness of $\mathcal C$ is an added hypothesis: if $\mathcal C=\emptyset$ the page's (3.5) holds ($\inf\emptyset=+\infty$) but no $v_\varepsilon\in\mathcal C$ exists. Constraints are indexed by `Fin m` (constraint $i$ of the page is Lean index $i-1$), $F'(v)$ is `fderiv ℝ F v` and $\|\cdot\|_*$ is the operator norm on `V →L[ℝ] ℝ`.
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 330, §3, Theorem 3.1, (3.5)–(3.7); standing setting pp. 329–330, (3.1)–(3.4)

import Mathlib
import Definitions.Def_EkelandVP_Constraints_feasibleSet
import Definitions.Def_EkelandVP_Constraints_IsRegular

namespace EkelandVP.Constraints

/-- Ekeland (1974), Theorem 3.1, p. 330: on a Banach space `V`, let `F` be Fréchet-differentiable and
`G_1, …, G_m` be `C¹` with the regularity assumption (3.4), and let `F` be bounded below on the
(nonempty) feasible set `𝒞` (3.5). Then for every `ε > 0` there is `v_ε ∈ 𝒞` with
`F(v_ε) ≤ inf_𝒞 F + ε²` (3.6), and reals `λ_1, …, λ_m` with `λ_i ≥ 0` for the inequality constraints,
`λ_i = 0` when `G_i(v_ε) ≠ 0`, and `‖F'(v_ε) - Σ λ_i G_i'(v_ε)‖* ≤ ε` (3.7). -/
theorem theorem_3_1 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {m : ℕ} (p : ℕ) (hp : p ≤ m) (F : V → ℝ) (G : Fin m → V → ℝ)
    (hF : Differentiable ℝ F) (hG : ∀ i, ContDiff ℝ 1 (G i))
    (hreg : IsRegular p G)
    (hne : (feasibleSet p G).Nonempty) (hbdd : BddBelow (F '' feasibleSet p G))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ v ∈ feasibleSet p G,
      (∀ w ∈ feasibleSet p G, F v ≤ F w + ε ^ 2) ∧
      ∃ lam : Fin m → ℝ,
        (∀ i : Fin m, p ≤ i.val → 0 ≤ lam i) ∧
        (∀ i : Fin m, G i v ≠ 0 → lam i = 0) ∧
        ‖fderiv ℝ F v - ∑ i, lam i • fderiv ℝ (G i) v‖ ≤ ε := by sorry

end EkelandVP.Constraints

-- Prove2me | Theorems.Thm_AggNash_Existence_lemma_5_5_3
-- name    : AggNash.Existence.lemma_5_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:05.346162+00:00
-- url     : https://prove2.me/theorems/517705b5-c561-41db-942c-5adef09d2da0
-- title:
--   Lemma 5.5 (3), p. 17 — f̃ᵢ(·, x₋ᵢ) is l.s.c. and convex, and conv(epi fᵢ) = epi f̃ᵢ = cl conv(epi fᵢ)
-- statement:
--   Work in the non-convex sum-aggregative game $\Gamma$ under the standing assumptions and Assumption 1, with $f_i$ the cost (2.1) and $\tilde f_i$ the convexified cost (2.2). Fix a player $i$ and $x_{-i}\in\tilde{\mathcal X}_{-i}$. Then $\tilde f_i(\cdot,x_{-i})$ is lower semicontinuous and convex on $\tilde{\mathcal X}_i=\operatorname{conv}\mathcal X_i$, and
--
--   $$
--   \operatorname{conv}\big(\operatorname{epi} f_i(\cdot,x_{-i})\big)=\operatorname{epi}\tilde f_i(\cdot,x_{-i})=\overline{\operatorname{conv}}\big(\operatorname{epi} f_i(\cdot,x_{-i})\big),
--   $$
--
--   where $\operatorname{epi} f_i(\cdot,x_{-i})=\{(y,t)\in\mathcal X_i\times\mathbb R \mid f_i(y,x_{-i})\le t\}$, $\operatorname{epi}\tilde f_i(\cdot,x_{-i})=\{(y,t)\in\tilde{\mathcal X}_i\times\mathbb R \mid \tilde f_i(y,x_{-i})\le t\}$, and $\overline{\operatorname{conv}}$ is the closure of the convex hull.
--
--   So $\tilde f_i(\cdot,x_{-i})$ is the convex envelope of $f_i(\cdot,x_{-i})$; its convexity and lower semicontinuity are what Theorem 5.3 needs to produce an equilibrium of $\tilde\Gamma$.
--
--   **Formalization Note** Epigraphs are subsets of $\mathbb R^d\times\mathbb R$ (`E d × ℝ`), and the closure is taken in the product topology.
-- source:
--   Liu, Oudjane & Wan, Approximate Nash equilibria in large non-convex aggregative games, arXiv:2011.12604v3, p. 17, Lemma 5.5 (3)

import Mathlib
import Definitions.Def_AggNash_Existence_Model

namespace AggNash.Existence

/-- Lemma 5.5 (3) (p. 17). Under Assumption 1, for each `x₋ᵢ ∈ 𝒳̃₋ᵢ`, the function
`f̃ᵢ(·, x₋ᵢ)` is lower semicontinuous and convex on `𝒳̃ᵢ`, and
`conv (epi fᵢ(·, x₋ᵢ)) = epi f̃ᵢ(·, x₋ᵢ) = cl conv (epi fᵢ(·, x₋ᵢ))`, where the epigraph of
`fᵢ(·, x₋ᵢ)` is taken over `𝒳ᵢ` and that of `f̃ᵢ(·, x₋ᵢ)` over `𝒳̃ᵢ`. -/
theorem lemma_5_5_3
    {n d q : ℕ} (X : Fin n → Set (E d)) (A : Fin n → (E d →L[ℝ] E q))
    (θ : Fin n → E d → E q → ℝ) (Ω : Set (E q)) (Δ M H γ : ℝ)
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ)
    (i : Fin n) (x : Fin n → E d) (hx : ∀ j, j ≠ i → x j ∈ convexHull ℝ (X j)) :
    LowerSemicontinuousOn (fun y => convCost X θ A i (Function.update x i y))
      (convexHull ℝ (X i)) ∧
    ConvexOn ℝ (convexHull ℝ (X i)) (fun y => convCost X θ A i (Function.update x i y)) ∧
    convexHull ℝ {p : E d × ℝ | p.1 ∈ X i ∧ cost θ A i (Function.update x i p.1) ≤ p.2} =
      {p : E d × ℝ | p.1 ∈ convexHull ℝ (X i) ∧
        convCost X θ A i (Function.update x i p.1) ≤ p.2} ∧
    {p : E d × ℝ | p.1 ∈ convexHull ℝ (X i) ∧
        convCost X θ A i (Function.update x i p.1) ≤ p.2} =
      closure (convexHull ℝ
        {p : E d × ℝ | p.1 ∈ X i ∧ cost θ A i (Function.update x i p.1) ≤ p.2}) := by sorry

end AggNash.Existence

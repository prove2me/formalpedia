-- Prove2me | Theorems.Thm_AggNash_Existence_lemma_5_5_1_2
-- name    : AggNash.Existence.lemma_5_5_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:02.493574+00:00
-- url     : https://prove2.me/theorems/8013f5ed-91d2-41b1-bf78-4f4e51769421
-- title:
--   Lemma 5.5 (1)–(2), p. 17 — f̃ᵢ ≤ fᵢ on 𝒳ᵢ, and the infimum in (2.2) is attained
-- statement:
--   Work in the non-convex sum-aggregative game $\Gamma$ under the standing assumptions and Assumption 1 (see the Model definitions), with $f_i$ the cost (2.1) and $\tilde f_i$ the convexified cost (2.2). Fix a player $i$ and a profile $x_{-i}\in\tilde{\mathcal X}_{-i}=\prod_{j\ne i}\operatorname{conv}\mathcal X_j$ of the other players. Then:
--
--   1. $\tilde f_i(x_i,x_{-i})\le f_i(x_i,x_{-i})$ for every $x_i\in\mathcal X_i$;
--   2. the infimum in (2.2) is attained at every $x_i\in\tilde{\mathcal X}_i$: there are $\alpha\in\mathcal S_d$ and $z^1,\dots,z^{d+1}\in\mathcal X_i$ with $x_i=\sum_k\alpha^kz^k$ and
--
--   $$
--   \sum_{k=1}^{d+1}\alpha^kf_i(z^k,x_{-i})=\tilde f_i(x_i,x_{-i}).
--   $$
--
--   Part (2) guarantees that generators $Z(i,x)$ exist at every profile of $\tilde\Gamma$.
--
--   **Formalization Note** The paper prints part (2) "for all $x_i\in\mathcal X_i$"; its proof takes an arbitrary point of $\tilde{\mathcal X}$, and Definition 2.2 needs minimizers at every $x\in\tilde{\mathcal X}$, so part (2) is stated on $\tilde{\mathcal X}_i$. $f_i(y,x_{-i})$ and $\tilde f_i(y,x_{-i})$ are evaluated at `Function.update x i y`.
-- source:
--   Liu, Oudjane & Wan, Approximate Nash equilibria in large non-convex aggregative games, arXiv:2011.12604v3, p. 17, Lemma 5.5 (1)–(2)

import Mathlib
import Definitions.Def_AggNash_Existence_Model

namespace AggNash.Existence

/-- Lemma 5.5 (1)–(2) (p. 17). Under Assumption 1, for each `x₋ᵢ ∈ 𝒳̃₋ᵢ`:
(1) `f̃ᵢ(xᵢ, x₋ᵢ) ≤ fᵢ(xᵢ, x₋ᵢ)` for all `xᵢ ∈ 𝒳ᵢ`;
(2) the infimum in (2.2) is attained at every `xᵢ ∈ 𝒳̃ᵢ = conv 𝒳ᵢ`. -/
theorem lemma_5_5_1_2
    {n d q : ℕ} (X : Fin n → Set (E d)) (A : Fin n → (E d →L[ℝ] E q))
    (θ : Fin n → E d → E q → ℝ) (Ω : Set (E q)) (Δ M H γ : ℝ)
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ)
    (i : Fin n) (x : Fin n → E d) (hx : ∀ j, j ≠ i → x j ∈ convexHull ℝ (X j)) :
    (∀ y ∈ X i, convCost X θ A i (Function.update x i y) ≤ cost θ A i (Function.update x i y)) ∧
    ∀ y ∈ convexHull ℝ (X i), ∃ α ∈ stdSimplex ℝ (Fin (d + 1)), ∃ z : Fin (d + 1) → E d,
      (∀ k, z k ∈ X i) ∧ ∑ k, α k • z k = y ∧
      ∑ k, α k * cost θ A i (Function.update x i (z k)) =
        convCost X θ A i (Function.update x i y) := by sorry

end AggNash.Existence

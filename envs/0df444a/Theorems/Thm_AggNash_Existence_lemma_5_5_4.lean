-- Prove2me | Theorems.Thm_AggNash_Existence_lemma_5_5_4
-- name    : AggNash.Existence.lemma_5_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:18.671835+00:00
-- url     : https://prove2.me/theorems/40fd154d-f736-4f24-9d15-42b69cd681bf
-- title:
--   Lemma 5.5 (4), p. 17 — f̃ᵢ and fᵢ attain equal minima (5.1); generators of a minimizer of f̃ᵢ minimize fᵢ
-- statement:
--   Work in the non-convex sum-aggregative game $\Gamma$ under the standing assumptions and Assumption 1, with $f_i$ the cost (2.1), $\tilde f_i$ the convexified cost (2.2), and generators as in Definition 2.2. Fix a player $i$ and $x_{-i}\in\tilde{\mathcal X}_{-i}$. Then:
--
--   1. $\tilde f_i(\cdot,x_{-i})$ attains its minimum on $\tilde{\mathcal X}_i$, and $f_i(\cdot,x_{-i})$ attains its minimum on $\mathcal X_i$;
--   2. the two minima are equal:
--
--   $$
--   \min_{\tilde x_i\in\tilde{\mathcal X}_i}\tilde f_i(\tilde x_i,x_{-i})=\min_{x_i\in\mathcal X_i}f_i(x_i,x_{-i}). \tag{5.1}
--   $$
--
--   3. In particular, if $\tilde x_i\in\tilde{\mathcal X}_i$ minimizes $\tilde f_i(\cdot,\tilde x_{-i})$ over $\tilde{\mathcal X}_i$, then every generator $Z(i,\tilde x)$ is contained in $\operatorname{arg\,min}_{y_i\in\mathcal X_i}f_i(y_i,\tilde x_{-i})$.
--
--   Part 3 is why a pure Nash equilibrium of the convexified game satisfies the full $0$-stability condition: every generator point is already a best reply in the original game.
--
--   **Formalization Note** The equality (5.1) is stated as: any minimizer of $\tilde f_i(\cdot,x_{-i})$ on $\tilde{\mathcal X}_i$ and any minimizer of $f_i(\cdot,x_{-i})$ on $\mathcal X_i$ have the same value. Generators are the positive-weight components of a minimizer of (2.2) (see the Model definitions); part 3 needs this reading.
-- source:
--   Liu, Oudjane & Wan, Approximate Nash equilibria in large non-convex aggregative games, arXiv:2011.12604v3, p. 17, Lemma 5.5 (4), (5.1) and the following 'In particular'

import Mathlib
import Definitions.Def_AggNash_Existence_Model

namespace AggNash.Existence

/-- Lemma 5.5 (4) and its "In particular" (p. 17). Under Assumption 1, for each `x₋ᵢ ∈ 𝒳̃₋ᵢ`,
both `f̃ᵢ(·, x₋ᵢ)` and `fᵢ(·, x₋ᵢ)` attain their minima on `𝒳̃ᵢ` and `𝒳ᵢ` respectively, and
the two minimum values are equal (5.1). In particular, if `x̃ᵢ ∈ argmin_{yᵢ ∈ 𝒳̃ᵢ} f̃ᵢ(yᵢ, x̃₋ᵢ)`,
then every generator `Z(i, x̃)` is contained in `argmin_{yᵢ ∈ 𝒳ᵢ} fᵢ(yᵢ, x̃₋ᵢ)`. -/
theorem lemma_5_5_4
    {n d q : ℕ} (X : Fin n → Set (E d)) (A : Fin n → (E d →L[ℝ] E q))
    (θ : Fin n → E d → E q → ℝ) (Ω : Set (E q)) (Δ M H γ : ℝ)
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ)
    (i : Fin n) (x : Fin n → E d) (hx : ∀ j, j ≠ i → x j ∈ convexHull ℝ (X j)) :
    (∃ y ∈ convexHull ℝ (X i), IsMinOn (fun y => convCost X θ A i (Function.update x i y))
      (convexHull ℝ (X i)) y) ∧
    (∃ y ∈ X i, IsMinOn (fun y => cost θ A i (Function.update x i y)) (X i) y) ∧
    (∀ y₁ ∈ convexHull ℝ (X i), ∀ y₂ ∈ X i,
      IsMinOn (fun y => convCost X θ A i (Function.update x i y)) (convexHull ℝ (X i)) y₁ →
      IsMinOn (fun y => cost θ A i (Function.update x i y)) (X i) y₂ →
      convCost X θ A i (Function.update x i y₁) = cost θ A i (Function.update x i y₂)) ∧
    (x i ∈ convexHull ℝ (X i) →
      IsMinOn (fun y => convCost X θ A i (Function.update x i y)) (convexHull ℝ (X i)) (x i) →
      ∀ Z : Set (E d), IsGenerator X θ A i x Z →
        ∀ y ∈ Z, y ∈ X i ∧ IsMinOn (fun y => cost θ A i (Function.update x i y)) (X i) y) := by sorry

end AggNash.Existence

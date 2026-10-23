-- Prove2me | Theorems.Thm_AggNash_Existence_theorem_2_7
-- name    : AggNash.Existence.theorem_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:22.098471+00:00
-- url     : https://prove2.me/theorems/a3365646-7434-495a-8c15-00ca76c98a06
-- title:
--   Theorem 2.7, p. 7 — an η-stable ε-PNE of Γ̃ disaggregates by (2.6) into an (ε + η + 2H(((√q+1)MΔ)/n)^γ)-PNE of Γ
-- statement:
--   Work in the non-convex sum-aggregative game $\Gamma$ under the standing assumptions and Assumption 1 (constants $\Delta$, $M$, $H$, $\gamma$; see the Model definitions). Let $\epsilon\ge0$ and $\eta\ge0$. Suppose that $\tilde x\in\tilde{\mathcal X}$ is an $\epsilon$-PNE of the convexified game $\tilde\Gamma$ that satisfies the $\eta$-stability condition with respect to a generator profile $(Z(i,\tilde x))_i$. Let $x^*$ be a profile with $x^*_i\in Z(i,\tilde x)$ for every $i$ such that
--
--   $$
--   x^*\in\operatorname*{arg\,min}_{x_i\in Z(i,\tilde x),\ i\in N}\Big\|\sum_{i\in N}A_i\tilde x_i-\sum_{i\in N}A_ix_i\Big\|^2. \tag{2.6}
--   $$
--
--   Then $x^*$ is an $\tilde\epsilon$-PNE of the non-convex game $\Gamma$, where
--
--   $$
--   \tilde\epsilon=\epsilon+\eta+2H\Big(\frac{(\sqrt q+1)M\Delta}{n}\Big)^\gamma .
--   $$
--
--   The error term vanishes as the number of players $n$ grows with $q$ fixed, so an approximate equilibrium of the convexified game yields an approximate equilibrium of the non-convex game.
--
--   **Formalization Note** The argmin (2.6) is stated as a minimality condition: $x^*$ is in $\prod_iZ(i,\tilde x)$ and its objective value is at most that of every profile in $\prod_iZ(i,\tilde x)$. Generators are the positive-weight components of a minimizer of (2.2). For $n=0$ Lean's $1/0=0$ makes the error term $0$; the statement is then about the empty profile and holds trivially.
-- source:
--   Liu, Oudjane & Wan, Approximate Nash equilibria in large non-convex aggregative games, arXiv:2011.12604v3, p. 7, Theorem 2.7, (2.6)

import Mathlib
import Definitions.Def_AggNash_Existence_Model

namespace AggNash.Existence

/-- Theorem 2.7 (p. 7). Under Assumption 1, let `x̃ ∈ 𝒳̃` be an `ε`-PNE of `Γ̃` satisfying
the `η`-stability condition with respect to a generator profile `(Z(i, x̃))ᵢ`, and let
`x* ∈ ∏ᵢ Z(i, x̃)` minimize `‖∑ᵢ Aᵢ x̃ᵢ − ∑ᵢ Aᵢ xᵢ‖²` over `∏ᵢ Z(i, x̃)` (2.6). Then `x*` is an
`ε̃`-PNE of `Γ` with `ε̃ = ε + η + 2H(((√q + 1) M Δ)/n)^γ`. -/
theorem theorem_2_7
    {n d q : ℕ} (X : Fin n → Set (E d)) (A : Fin n → (E d →L[ℝ] E q))
    (θ : Fin n → E d → E q → ℝ) (Ω : Set (E q)) (Δ M H γ : ℝ)
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ)
    (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η) (xt : Fin n → E d)
    (hxt : IsEpsPNE (fun i => convexHull ℝ (X i)) (convCost X θ A) ε xt)
    (Z : Fin n → Set (E d)) (hZ : ∀ i, IsGenerator X θ A i xt (Z i))
    (hstab : IsStable X θ A η xt Z)
    (xs : Fin n → E d) (hxs : ∀ i, xs i ∈ Z i)
    (hmin : ∀ x' : Fin n → E d, (∀ i, x' i ∈ Z i) →
      ‖∑ i, A i (xt i) - ∑ i, A i (xs i)‖ ^ 2 ≤ ‖∑ i, A i (xt i) - ∑ i, A i (x' i)‖ ^ 2) :
    IsEpsPNE X (cost θ A)
      (ε + η + 2 * H * (((Real.sqrt (q : ℝ) + 1) * M * Δ) / (n : ℝ)) ^ γ) xs := by sorry

end AggNash.Existence

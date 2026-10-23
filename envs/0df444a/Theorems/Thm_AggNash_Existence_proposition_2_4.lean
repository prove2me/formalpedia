-- Prove2me | Theorems.Thm_AggNash_Existence_proposition_2_4
-- name    : AggNash.Existence.proposition_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:15.324564+00:00
-- url     : https://prove2.me/theorems/a8072208-1a03-4af6-acc2-6917fb6ed742
-- title:
--   Proposition 2.4, p. 6 — a non-convex sum-aggregative game has a 2H(((√q+1)MΔ)/n)^γ-PNE; any disaggregation (2.4) of a PNE of Γ̃ is one
-- statement:
--   Work in the non-convex sum-aggregative game $\Gamma$ of the Model definitions: $n$ players with compact, nonempty, possibly non-convex action sets $\mathcal X_i\subset\mathbb R^d$ of diameter at most $\Delta>0$, costs $f_i(x_i,x_{-i})=\theta_i(x_i,\frac1n\sum_jA_jx_j)$ with $q\times d$ matrices $\|A_j\|_2\le M$, $M>0$, and $\Omega$ a neighbourhood of the aggregate set of $\tilde{\mathcal X}$. Under Assumption 1 (lower semicontinuity of $\theta_i$ in the own action and $(H,\gamma)$-Hölder continuity in the aggregate), set
--
--   $$
--   \epsilon=2H\Big(\frac{(\sqrt q+1)M\Delta}{n}\Big)^\gamma .
--   $$
--
--   Then:
--
--   1. the non-convex game $\Gamma$ admits an $\epsilon$-pure Nash equilibrium;
--   2. more precisely, if $\tilde x\in\tilde{\mathcal X}$ is a pure Nash equilibrium of the convexified game $\tilde\Gamma$ and $Z(i,\tilde x)$ is an arbitrary generator for each player $i$, then every profile $x^*$ with $x^*_i\in Z(i,\tilde x)$ for all $i$ and
--
--   $$
--   x^*\in\operatorname*{arg\,min}_{x_i\in Z(i,\tilde x),\ i\in N}\Big\|\sum_{i\in N}A_i\tilde x_i-\sum_{i\in N}A_ix_i\Big\|^2 \tag{2.4}
--   $$
--
--   is an $\epsilon$-pure Nash equilibrium of $\Gamma$.
--
--   Without convexity a pure Nash equilibrium need not exist; the result shows that in a large aggregative game an approximate one does, with an error of order $n^{-\gamma}$ for fixed $q$, and that it can be built from an equilibrium of the convexified game.
--
--   **Formalization Note** The argmin (2.4) is stated as a minimality condition over $\prod_iZ(i,\tilde x)$. Generators are the positive-weight components of a minimizer of (2.2), and the action sets are assumed nonempty (see the Model definitions). For $n=0$ Lean's $1/0=0$ makes $\epsilon=0$, and the statement holds for the empty profile.
-- source:
--   Liu, Oudjane & Wan, Approximate Nash equilibria in large non-convex aggregative games, arXiv:2011.12604v3, p. 6, Proposition 2.4, (2.4)

import Mathlib
import Definitions.Def_AggNash_Existence_Model

namespace AggNash.Existence

/-- Proposition 2.4 (p. 6). Under Assumption 1, the non-convex game `Γ` admits an `ε`-PNE with
`ε = 2H(((√q + 1) M Δ)/n)^γ`. In particular, if `x̃` is a PNE of `Γ̃` and `Z(i, x̃)` is an
arbitrary generator for each player `i`, then every `x* ∈ ∏ᵢ Z(i, x̃)` minimizing
`‖∑ᵢ Aᵢ x̃ᵢ − ∑ᵢ Aᵢ xᵢ‖²` over `∏ᵢ Z(i, x̃)` (2.4) is an `ε`-PNE of `Γ`. -/
theorem proposition_2_4
    {n d q : ℕ} (X : Fin n → Set (E d)) (A : Fin n → (E d →L[ℝ] E q))
    (θ : Fin n → E d → E q → ℝ) (Ω : Set (E q)) (Δ M H γ : ℝ)
    (hstd : StandingHyp X A Ω Δ M) (hA1 : Assumption1 X Ω θ H γ) :
    (∃ x : Fin n → E d, IsEpsPNE X (cost θ A)
      (2 * H * (((Real.sqrt (q : ℝ) + 1) * M * Δ) / (n : ℝ)) ^ γ) x) ∧
    ∀ xt : Fin n → E d, IsEpsPNE (fun i => convexHull ℝ (X i)) (convCost X θ A) 0 xt →
      ∀ Z : Fin n → Set (E d), (∀ i, IsGenerator X θ A i xt (Z i)) →
      ∀ xs : Fin n → E d, (∀ i, xs i ∈ Z i) →
      (∀ x' : Fin n → E d, (∀ i, x' i ∈ Z i) →
        ‖∑ i, A i (xt i) - ∑ i, A i (xs i)‖ ^ 2 ≤ ‖∑ i, A i (xt i) - ∑ i, A i (x' i)‖ ^ 2) →
      IsEpsPNE X (cost θ A)
        (2 * H * (((Real.sqrt (q : ℝ) + 1) * M * Δ) / (n : ℝ)) ^ γ) xs := by sorry

end AggNash.Existence

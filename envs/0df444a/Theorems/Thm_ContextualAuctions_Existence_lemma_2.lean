-- Prove2me | Theorems.Thm_ContextualAuctions_Existence_lemma_2
-- name    : ContextualAuctions.Existence.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:29:53.513668+00:00
-- url     : https://prove2.me/theorems/751b67bd-a135-4d15-8f37-f1ce9535c095
-- title:
--   Lemma 2, p. 10 — ℓ^µ is nondecreasing in each component of w and nonincreasing in B
-- statement:
--   Work in the contextual first price auction model with budgets (see the `Setting` and `FixedPoint` modules), under its standing assumptions. Let $\mu:\Theta\to[0,\omega/B_{\min}]$ be a pacing function and let $\ell^\mu(w,B)$ be the smallest minimizer of $t\mapsto q^\mu(w,B,t)$ over $[0,\omega/B_{\min}]$. Then:
--
--   1. $\ell^\mu$ is nondecreasing in each component of $w$: if $(w,B),(w',B)\in\Theta$ agree in every coordinate except the $i$-th and $w_i\le w'_i$, then $\ell^\mu(w,B)\le\ell^\mu(w',B)$.
--   2. $\ell^\mu$ is nonincreasing as a function of $B$: if $(w,B),(w,B')\in\Theta$ and $B\le B'$, then
--   $$
--   \ell^\mu(w,B')\le\ell^\mu(w,B).
--   $$
--
--   Buyers who value items more pace more, and buyers with larger budgets pace less. The monotonicity is what bounds the total variation of $\ell^\mu$ in Lemma 3.
--
--   **Formalization Note** "In each component" is stated on sections: one coordinate of $w$ varies while the other coordinates and $B$ are fixed, with both points in $\Theta$. The pacing function is assumed measurable.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 10, Lemma 2

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_Setting
import Definitions.Def_ContextualAuctions_Existence_FixedPoint

namespace ContextualAuctions.Existence

theorem lemma_2 (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (hμ : IsPacing M μ)
    (hμr : ∀ θ ∈ Theta M, μ θ ∈ Set.Icc 0 (omega M / M.Bmin)) :
    (∀ θ ∈ Theta M, ∀ θ' ∈ Theta M, ∀ i : Fin M.d, θ.2 = θ'.2 → (∀ j, j ≠ i → θ.1 j = θ'.1 j) →
        θ.1 i ≤ θ'.1 i → ell M μ θ ≤ ell M μ θ') ∧
      (∀ θ ∈ Theta M, ∀ θ' ∈ Theta M, θ.1 = θ'.1 → θ.2 ≤ θ'.2 → ell M μ θ' ≤ ell M μ θ) := by sorry

end ContextualAuctions.Existence

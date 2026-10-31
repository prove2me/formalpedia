-- Prove2me | Theorems.Thm_DPDeconstructed_g_greedy_exists
-- name    : DPDeconstructed.g_greedy_exists
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:49:15.547216+00:00
-- url     : https://prove2.me/theorems/6acca12f-4fa2-49a5-8b15-c7a81d2e33e4
-- title:
--   §3.1, p.14 — a $g$-greedy policy exists for every $g\in\mathbb G$
-- statement:
--   Let a dynamic program satisfy Assumption 2.1 for the set $\mathbb V$ and let $(W_0,W_1)$ be a plan factorization, $\mathbb G=W_0\mathbb V$. For every $g\in\mathbb G$ there is a feasible policy $\sigma$ that is $g$-greedy:
--
--   $$M_\sigma W_1g=MW_1g\quad\text{pointwise on }\mathsf X.$$
--
--   This is how the refactored Bellman equation produces policies; the proof of Theorem 3.3 applies it to the fixed point of $S$.
--
--   Differences from the source:
--   - encoding: M_σ W₁ g = M W₁ g → equality in EReal at every x; reason: M W₁ g is an extended-real supremum; same equation
--   - encoding: plan factorization: W₀ defined on 𝒱 with values in 𝒢, W₁ defined on 𝒢 with values in ℋ, and (7) → structure with total maps W₀ on ℝ^X, W₁ on ℝ^F and the single field (7); reason: 𝒢 := W₀𝒱 gives the first condition and (7) gives the second; values off 𝒱 and 𝒢 never enter a statement, so every pair on the page is an instance
--   - encoding: 𝕍 is the set whose existence Assumption 2.1 asserts → 𝕍 is a parameter with the hypothesis Assumption21 𝕍; reason: the statement holds for each such set, which covers the one the paper fixes; 𝔾 and the domain of S depend on it
-- source:
--   Ma and Stachurski, Dynamic Programming Deconstructed: Transformations of the Bellman Equation and Computational Efficiency, arXiv:1811.01940v2, §3.1, p.14 (unnumbered, after the definition of g-greedy)

import Mathlib
import Definitions.Def_DPDeconstructed_PlanFactorization

namespace DPDeconstructed

open DynProg PlanFactorization

/-- Ma and Stachurski, *Dynamic Programming Deconstructed*, arXiv:1811.01940v2, §3.1, p.14
(unnumbered): "At least one `g`-greedy policy exists for every `g ∈ 𝔾`." Here the dynamic
program satisfies Assumption 2.1 for the set `𝕍`, `(W₀, W₁)` is a plan factorization,
`𝔾 = W₀ 𝕍`, and `σ ∈ Σ` is `g`-greedy if `M_σ W₁ g = M W₁ g`. -/
theorem g_greedy_exists {X A : Type*} [Nonempty X] (D : DynProg X A) (𝕍 : Set (X → ℝ))
    (h21 : D.Assumption21 𝕍) (P : PlanFactorization D) :
    ∀ g ∈ P.bbG 𝕍, ∃ σ : D.Policy, P.IsGGreedy g σ := by sorry

end DPDeconstructed

-- Prove2me | Theorems.Thm_ContextualAuctions_Structure_proposition_3
-- name    : ContextualAuctions.Structure.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:29:28.822079+00:00
-- url     : https://prove2.me/theorems/028fb40c-c374-4eb8-b070-fc27a5ca6d95
-- title:
--   Proposition 3, p. 14 — colinear paced buyers with equal budgets are paced to one weight vector, the largest unpaced one if it exists
-- statement:
--   Assume the model's standing assumptions and the standing assumptions of §6: zero reserve prices, a convex compact support $\delta(G) \subseteq \Theta$ of the type law $G$, and a pacing function $\mu$ such that $\mu(w,B)$ is the unique minimizer of $t \mapsto q^\mu(w,B,t)$ over $[0,\omega/B_{\min}]$ for every $(w,B) \in \delta(G)$. Call a type $(w,B)$ *unpaced* if $\mu(w,B) = 0$ and *paced* otherwise; $\|\cdot\|$ is the Euclidean norm.
--
--   Let $\hat w \in \mathbb{R}^d$ be a unit vector with strictly positive entries and $B > 0$ a budget such that $w/\|w\| = \hat w$ for some $(w,B) \in \delta(G)$. Then:
--
--   1. Paced buyers with budget $B$ and weight vectors along $\hat w$ have identical paced weight vectors: if $(w_1,B), (w_2,B) \in \delta(G)$, $w_1/\|w_1\| = w_2/\|w_2\| = \hat w$ and $\mu(w_1,B), \mu(w_2,B) > 0$, then
--   $$\frac{w_1}{1+\mu(w_1,B)} = \frac{w_2}{1+\mu(w_2,B)}.$$
--   2. Suppose some $(w,B) \in \delta(G)$ with $w/\|w\| = \hat w$ is unpaced. Then the largest unpaced weight vector along $\hat w$,
--   $$w_0 = \operatorname*{arg\,max}\big\{\|w\| : (w,B) \in \delta(G),\ \mu(w,B) = 0,\ w/\|w\| = \hat w\big\},$$
--   exists, and every paced weight vector along $\hat w$ is paced down to it:
--   $$\frac{w}{1+\mu(w,B)} = w_0 \quad\text{for all } (w,B) \in \delta(G) \text{ with } w/\|w\| = \hat w,\ \mu(w,B) > 0.$$
--
--   Combined with complementary slackness, buyers with the same budget, positive pacing multipliers and proportional weight vectors are paced down to the one type that exactly spends that budget; scaling up a budget-constrained buyer's weights without changing the budget does not change the equilibrium outcome.
--
--   **Formalization Note.** Part 2 asserts the existence of the maximizer $w_0$, which the paper presupposes by writing "let $w_0 = \arg\max\{\dots\}$". The maximization set and the final quantifier "for all $w \in \delta(G)$" are read with the budget fixed, i.e. over $(w, B) \in \delta(G)$, since $\mu$ is defined on $\Theta$ and the uniqueness hypothesis binds only on $\delta(G)$. The positivity of $\hat w$ and $B > 0$ are the paper's hypotheses; both also follow from $\delta(G) \subseteq \Theta$. Unit vectors and norms are Euclidean, and $w/\|w\|$ is written $\|w\|^{-1} w$.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 14, Proposition 3

import Mathlib
import Definitions.Def_ContextualAuctions_Structure_Setting
import Definitions.Def_ContextualAuctions_Structure_Structural

namespace ContextualAuctions.Structure

theorem proposition_3 (M : Model) (hM : M.Standing) (mu : (Fin M.d → ℝ) × ℝ → ℝ)
    (h6 : SixStanding M mu) (what : Fin M.d → ℝ) (hunit : wnorm what = 1)
    (hpos : ∀ i, 0 < what i) (B : ℝ) (hB : 0 < B)
    (hray : ∃ w, (w, B) ∈ supp M ∧ (wnorm w)⁻¹ • w = what) :
    (∀ w₁ w₂ : Fin M.d → ℝ, (w₁, B) ∈ supp M → (w₂, B) ∈ supp M →
        (wnorm w₁)⁻¹ • w₁ = what → (wnorm w₂)⁻¹ • w₂ = what →
        0 < mu (w₁, B) → 0 < mu (w₂, B) →
        (1 + mu (w₁, B))⁻¹ • w₁ = (1 + mu (w₂, B))⁻¹ • w₂) ∧
    ((∃ w, (w, B) ∈ supp M ∧ (wnorm w)⁻¹ • w = what ∧ mu (w, B) = 0) →
      ∃ w₀ : Fin M.d → ℝ,
        ((w₀, B) ∈ supp M ∧ (wnorm w₀)⁻¹ • w₀ = what ∧ mu (w₀, B) = 0) ∧
        (∀ w, (w, B) ∈ supp M → (wnorm w)⁻¹ • w = what → mu (w, B) = 0 →
          wnorm w ≤ wnorm w₀) ∧
        ∀ w, (w, B) ∈ supp M → (wnorm w)⁻¹ • w = what → 0 < mu (w, B) →
          (1 + mu (w, B))⁻¹ • w = w₀) := by sorry

end ContextualAuctions.Structure

-- Prove2me | Theorems.Thm_ContextualAuctions_Existence_lemma_1
-- name    : ContextualAuctions.Existence.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T19:28:58.517073+00:00
-- url     : https://prove2.me/theorems/b3140264-0abf-4376-967b-ece15d4d6db7
-- title:
--   Lemma 1, p. 8 — the paced first-price bid σ^µ_α(wᵀα/(1+t)) maximizes the Lagrangian for multiplier t
-- statement:
--   Work in the contextual first price auction model with budgets (see the `Setting` module), under its standing assumptions. Let $\mu$ be a pacing function, $(w,B)\in\Theta$ a buyer type and $t\ge0$ a dual multiplier. Suppose all competitors use the value pacing–based strategy $\beta^\mu$. Then the bid function $\alpha\mapsto\sigma^\mu_\alpha\big(w^T\alpha/(1+t)\big)$ is admissible and
--
--   $$
--   \sigma^\mu_\alpha\Big(\frac{w^T\alpha}{1+t}\Big)\in\arg\max_{b(\cdot)}\ \mathbb E_{\alpha,\{\theta_i\}_{i=1}^{n-1}}\Big[\Big(\frac{w^T\alpha}{1+t}-b(\alpha)\Big)\mathbb 1\{b(\alpha)\ge\max(r(\alpha),\{\beta^\mu(\theta_i,\alpha)\}_i)\}\Big].
--   $$
--
--   The maximum is over all admissible bid functions $b:A\to\mathbb R_{\ge0}$. This is the Lagrangian optimality step in the proof that $\beta^\mu$ is a best response to itself: a buyer who acts as if its value were $w^T\alpha/(1+t)$ is best off bidding as in an unconstrained i.i.d. first price auction against paced competitors.
--
--   **Formalization Note** The claim holds for every type in $\Theta$ and every $t\ge0$, not only almost surely. Admissible bids are measurable, nonnegative on $A$, and have an integrable payment.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 8, Lemma 1

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_Setting

namespace ContextualAuctions.Existence

theorem lemma_1 (M : Model) (hM : M.Standing) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (hμ : IsPacing M μ)
    (θ : (Fin M.d → ℝ) × ℝ) (hθ : θ ∈ Theta M) (t : ℝ) (ht : 0 ≤ t) :
    Admissible M (beta M μ) (fun α => sigma M μ α (val θ α / (1 + t))) ∧
      ∀ b, Admissible M (beta M μ) b →
        lagr M μ θ t b ≤ lagr M μ θ t (fun α => sigma M μ α (val θ α / (1 + t))) := by sorry

end ContextualAuctions.Existence

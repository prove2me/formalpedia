-- Prove2me | Theorems.Thm_ContextualAuctions_Structure_mu_monotone
-- name    : ContextualAuctions.Structure.mu_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:29:21.973999+00:00
-- url     : https://prove2.me/theorems/4fde75ec-856e-405a-bdb9-9b895bb4ab8a
-- title:
--   §6, p. 14 — under a unique best response, µ(w,B) is nondecreasing in each w_i and nonincreasing in B on δ(G)
-- statement:
--   Assume the model's standing assumptions and the standing assumptions of §6: zero reserve prices, a convex compact support $\delta(G) \subseteq \Theta$ of the type law, and a pacing function $\mu$ such that $\mu(w,B)$ is the unique minimizer of $t \mapsto q^\mu(w,B,t)$ over $[0, \omega/B_{\min}]$ for every $(w,B) \in \delta(G)$. Then $\mu$ is monotone in the buyer type on $\delta(G)$:
--
--   1. (nondecreasing in each weight) if $(w,B), (w',B) \in \delta(G)$ differ only in one coordinate $i$ and $w_i \le w'_i$, then
--   $$\mu(w,B) \le \mu(w',B);$$
--   2. (nonincreasing in the budget) if $(w,B), (w,B') \in \delta(G)$ and $B \le B'$, then
--   $$\mu(w,B') \le \mu(w,B).$$
--
--   Intuitively, a buyer with a smaller budget must shade bids more aggressively to meet it, while a larger weight raises the paced values, the number of auctions won and the expenditure, which again calls for more pacing. This monotonicity is one of the structural properties behind Proposition 3.
--
--   **Formalization Note.** The paper derives this from its Lemma 2 (the smallest dual minimizer $\ell^\mu$ is monotone on $\Theta$): under a unique best response, $\mu = \ell^\mu$ on $\delta(G)$. The statement is posed on $\delta(G)$, where uniqueness is assumed, comparing types that differ in one coordinate only; since $\delta(G)$ is convex, the segment between two such types stays in $\delta(G)$.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 14, §6, second paragraph (consequence of Lemma 2, p. 10)

import Mathlib
import Definitions.Def_ContextualAuctions_Structure_Setting
import Definitions.Def_ContextualAuctions_Structure_Structural

namespace ContextualAuctions.Structure

theorem mu_monotone (M : Model) (hM : M.Standing) (mu : (Fin M.d → ℝ) × ℝ → ℝ)
    (h6 : SixStanding M mu) :
    (∀ (w w' : Fin M.d → ℝ) (B : ℝ) (i : Fin M.d), (w, B) ∈ supp M → (w', B) ∈ supp M →
        (∀ j, j ≠ i → w j = w' j) → w i ≤ w' i → mu (w, B) ≤ mu (w', B)) ∧
    (∀ (w : Fin M.d → ℝ) (B B' : ℝ), (w, B) ∈ supp M → (w, B') ∈ supp M → B ≤ B' →
        mu (w, B') ≤ mu (w, B)) := by sorry

end ContextualAuctions.Structure

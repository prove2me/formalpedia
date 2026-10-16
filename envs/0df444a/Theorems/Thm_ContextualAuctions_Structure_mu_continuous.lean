-- Prove2me | Theorems.Thm_ContextualAuctions_Structure_mu_continuous
-- name    : ContextualAuctions.Structure.mu_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:29:22.225511+00:00
-- url     : https://prove2.me/theorems/b05d05c2-6d64-4ffc-9843-1c44b4ab5787
-- title:
--   §6, p. 14 — under a unique best response, the pacing function µ is continuous on δ(G)
-- statement:
--   Assume the model's standing assumptions and the standing assumptions of §6: zero reserve prices, a convex compact support $\delta(G) \subseteq \Theta$ of the type law $G$, and a pacing function $\mu$ such that $\mu(w,B)$ is the unique minimizer of $t \mapsto q^\mu(w,B,t)$ over $[0,\omega/B_{\min}]$ for every $(w,B) \in \delta(G)$. Then
--   $$\mu \text{ restricted to } \delta(G) \text{ is continuous.}$$
--
--   Continuity of the pacing function is what makes the largest unpaced weight vector of Proposition 3 exist, and it is one of the two structural properties (with monotonicity) the paper uses to describe the equilibrium pacing multipliers.
--
--   **Formalization Note.** The paper says "µ is continuous" without naming the domain and refers to Lemma 14 of its online appendix. Continuity is posed on $\delta(G)$, the set on which the unique-best-response hypothesis is made; off $\delta(G)$ the hypotheses do not constrain $\mu$.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 14, §6, second paragraph, last sentence (Lemma 14 of the online appendix)

import Mathlib
import Definitions.Def_ContextualAuctions_Structure_Setting
import Definitions.Def_ContextualAuctions_Structure_Structural

namespace ContextualAuctions.Structure

theorem mu_continuous (M : Model) (hM : M.Standing) (mu : (Fin M.d → ℝ) × ℝ → ℝ)
    (h6 : SixStanding M mu) : ContinuousOn mu (supp M) := by sorry

end ContextualAuctions.Structure

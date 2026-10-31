-- Prove2me | Theorems.Thm_FMLPricing_BranchBound_proposition_1
-- name    : FMLPricing.BranchBound.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:40.558374+00:00
-- url     : https://prove2.me/theorems/fb4239ad-5197-436a-aebc-52efb8b165dc
-- title:
--   Proposition 1, p. 10 — a global revenue maximizer exists and every one lies in the price box [p̲, p̄]
-- statement:
--   Consider the finite-mixture logit revenue $\Pi(p) = \sum_{c} w_c \sum_j p_j q_{cj}(p)$ on $\mathbb R^n$, under the standing assumptions ($m, n \ge 1$, $w_c > 0$ with $\sum_c w_c = 1$, $b_j > 0$). Let
--   $$
--   \underline p_j = b_j^{-1}, \qquad \bar p_j = b_j^{-1} + \max_{c \in M}\, \max_{p \in \mathbb R^n} \sum_{i \in N} p_i\, q_{ci}(p), \qquad j \in N.
--   $$
--   Then $\Pi$ has a global maximizer, and every global maximizer $p^\star$ satisfies
--   $$
--   \underline p_j \le p^\star_j \le \bar p_j \quad \text{for all } j \in N.
--   $$
--
--   The result reduces the price search to the compact box $[\underline p, \bar p]$, on which the no-purchase reparameterization and Algorithm 1 operate.
--
--   **Formalization Note** The inner maximum in $\bar p_j$ is the real supremum of the single-segment revenue over $\mathbb R^n$; it is bounded above by $\sum_i e^{a_{ci}-1}/b_i$.
-- source:
--   van de Geer & den Boer, Price Optimization Under the Finite-Mixture Logit Model, SSRN 3235432 (version of August 26, 2021), p. 10, Proposition 1 (proof pp. 30–33)

import Mathlib
import Definitions.Def_FMLPricing_BranchBound_Model

namespace FMLPricing.BranchBound

/-- Proposition 1, p. 10: a global maximizer of `Π` exists, and every global maximizer
lies in the box `[p̲, p̄]`. -/
theorem proposition_1 {m n : ℕ} (I : FML m n) (hI : Standing I) :
    (∃ pstar : Fin n → ℝ, ∀ p, Pi I p ≤ Pi I pstar) ∧
      ∀ pstar : Fin n → ℝ, (∀ p, Pi I p ≤ Pi I pstar) →
        ∀ j, pLo I j ≤ pstar j ∧ pstar j ≤ pHi I j := by sorry

end FMLPricing.BranchBound

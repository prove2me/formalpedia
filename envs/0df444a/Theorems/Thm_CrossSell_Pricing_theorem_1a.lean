-- Prove2me | Theorems.Thm_CrossSell_Pricing_theorem_1a
-- name    : CrossSell.Pricing.theorem_1a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:18.697437+00:00
-- url     : https://prove2.me/theorems/a86bd098-4da0-4217-b358-c3365ee29692
-- title:
--   Theorem 1(a), p. 12 — at every optimal (p, r) the aggregate markup p_i − c_i + t_i is the same for all main products in S
-- statement:
--   In the sequential multinomial logit model (main offer set $S$, secondary sets $T_i$, utilities $u_i, v_{il}$, costs $c_i, s_l$), let $(\mathbf p, \mathbf r)$ maximize the total expected profit $\Pi(S,\mathbf T,\cdot,\cdot)$ over all main and secondary price vectors. Then for all $i, j \in S$,
--   $$p_i - c_i + t_i(\mathbf r) = p_j - c_j + t_j(\mathbf r),$$
--   where $t_i(\mathbf r) = \sum_{l\in T_i}(r_l - s_l)\exp(v_{il} - r_l)/\big(1 + \sum_{k\in T_i}\exp(v_{ik} - r_k)\big)$.
--
--   That is, the aggregate markup of Definition 1 is the same across all main products at optimality. This collapses the choice of the main prices to a single scalar, which is what reduces problem (6) to the secondary-price problem.
--
--   **Formalization Note.** "At optimality" is a global maximizer of $\Pi$ over $(\mathbf p, \mathbf r) \in \mathbb R^{\mathcal M}\times\mathbb R^{\mathcal N}$ with $S$ and $\mathbf T$ fixed, as in the paper's pricing problem; prices carry no sign constraints.
-- source:
--   Ke & Wang, Cross-Category Retailing Management: Substitution and Complementarity, accepted manuscript (SSRN 3383023), p. 12, Theorem 1(a)

import Mathlib
import Definitions.Def_CrossSell_Pricing_Model

namespace CrossSell.Pricing

theorem theorem_1a {ι κ : Type*} (S : Finset ι) (T : Option ι → Finset κ)
    (u c : ι → ℝ) (s : κ → ℝ) (v : Option ι → κ → ℝ) (p : ι → ℝ) (r : κ → ℝ)
    (hopt : ∀ (p' : ι → ℝ) (r' : κ → ℝ), profit S T u c s v p' r' ≤ profit S T u c s v p r) :
    ∀ i ∈ S, ∀ j ∈ S, aggMarkup T c s v p r i = aggMarkup T c s v p r j := by sorry

end CrossSell.Pricing

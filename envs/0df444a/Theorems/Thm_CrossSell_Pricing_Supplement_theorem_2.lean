-- Prove2me | Theorems.Thm_CrossSell_Pricing_Supplement_theorem_2
-- name    : CrossSell.Pricing.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:52:31.231563+00:00
-- url     : https://prove2.me/theorems/7535128e-b76e-4535-a8a8-b1dbc3929727
-- title:
--   Theorem 2 — pair markup invariance with disjoint secondary sets
-- statement:
--   Fix finite main and secondary universes, any main assortment S, secondary sets T_i, utilities u_i and v_il, and costs c_i and s_l. Suppose the secondary sets are pairwise disjoint across distinct outcomes in S+, including outside outcome 0. Let (p,r) globally maximize the published true profit over all real main and secondary price vectors. Then, for every i,j in S, l in T_i and k in T_j,
--   $$p_i-c_i+r_l-s_l=p_j-c_j+r_k-s_k.$$
--   This extends equal aggregate markups to every pair of a main product and an associated secondary product, across distinct main products as well as within one secondary set. The conclusion has its literal vacuous meaning when there are no associated pairs.
--
--   Differences from the source:
--   - encoding: finite labeled products and the outcome 0 → finite types and Option for S+, with genuine global price maximality; reason: this preserves the model, outside outcome, unconstrained prices, and all compared pairs
-- source:
--   Ke & Wang, Cross-Category Retailing Management: Substitution and Complementarity, accepted manuscript (SSRN 3383023), p. 15, Theorem 2

import Mathlib
import Definitions.Def_CrossSell_Pricing_Supplement_PricingPolicy

namespace CrossSell.Pricing.Supplement

theorem theorem_2 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (S : Finset ι) (T : Option ι → Finset κ) (u c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (p : ι → ℝ) (r : κ → ℝ)
    (hdisjoint : DisjointSecondary S T)
    (hopt : ∀ p' r', profit S T u c s v p' r' ≤ profit S T u c s v p r) :
    ∀ i ∈ S, ∀ l ∈ T (some i), ∀ j ∈ S, ∀ k ∈ T (some j),
      p i - c i + r l - s l = p j - c j + r k - s k := by sorry

end CrossSell.Pricing.Supplement

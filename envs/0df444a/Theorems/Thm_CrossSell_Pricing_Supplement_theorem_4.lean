-- Prove2me | Theorems.Thm_CrossSell_Pricing_Supplement_theorem_4
-- name    : CrossSell.Pricing.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:53:35.763161+00:00
-- url     : https://prove2.me/theorems/8e703f80-9f1d-4876-b89d-edc23e337a28
-- title:
--   Theorem 4 — for an optimal secondary configuration, every aggregate-markup relabeling has an optimal prefix
-- statement:
--   Fix arbitrary real prices p,r, utilities u,v and costs c,s on finite main and secondary universes. Let F be a nonempty finite family of complete feasible secondary configurations T_i on all main outcomes and outside outcome 0; F is fixed independently of the main offer set. Then there is T in F with the following property: for every relabeling sigma of all main products in weakly decreasing order of the aggregate markup p_i-c_i+t_i(T_i) computed for that very T (any tie-breaking), some prefix S_m={sigma(1),...,sigma(m)}, 0<=m<=M, satisfies
--   $$\Pi(S',T',p,r)\le\Pi(S_m,T,p,r)\qquad\text{for every }T'\in F\text{ and every }S'\subseteq\mathcal M.$$
--   The optimum is actually attained by a feasible configuration, and the conclusion does not depend on how ties in the relabeling are broken (a sorted relabeling always exists, so the conclusion is never vacuous). Arbitrary overlaps, disjoint sets, and identical-set restrictions can all be represented by F. Outside secondary sales remain in the objective and margins may have either sign. This gives the main-assortment structure at a joint optimizer of problem (13).
--
--   Differences from the source:
--   - encoding: all feasible secondary offers in (13) → a nonempty finite family of complete configurations independent of S; reason: the product universes are finite, so any feasible family is finite; nonemptiness states that the optimization problem is feasible
--   - reading: Definition 3 writes prefixes without specifying the zero-length boundary → prefix length zero is included; reason: problem (13) permits the empty main assortment; with negative main margins it can be the only optimum, so no instance is removed
-- source:
--   Ke & Wang, Cross-Category Retailing Management: Substitution and Complementarity, accepted manuscript (SSRN 3383023), p. 19, Theorem 4

import Mathlib
import Definitions.Def_CrossSell_Pricing_Supplement_Assortment

namespace CrossSell.Pricing.Supplement

/-- For an optimal feasible configuration T, every relabeling of the main products in
    decreasing aggregate markup (any tie-breaking) has an optimal prefix. -/
theorem theorem_4 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (F : Finset (Option ι → Finset κ)) (hF : F.Nonempty)
    (u c p : ι → ℝ) (s r : κ → ℝ) (v : Option ι → κ → ℝ) :
    ∃ T ∈ F, ∀ σ : Fin (Fintype.card ι) ≃ ι, Sorted (aggMarkup T c s v p r) σ →
      ∃ m : ℕ, m ≤ Fintype.card ι ∧
        ∀ T' ∈ F, ∀ S' : Finset ι,
          profit S' T' u c s v p r ≤ profit (offerPrefix σ m) T u c s v p r := by sorry

end CrossSell.Pricing.Supplement

-- Prove2me | Theorems.Thm_CrossSell_Pricing_Supplement_theorem_3
-- name    : CrossSell.Pricing.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:53:07.898832+00:00
-- url     : https://prove2.me/theorems/f3aaa20a-7d51-4f1c-b434-7acea6ab67e9
-- title:
--   Theorem 3 (corrected: nonnegative spread budget) — exp(−2δ) guarantee for constructed prices
-- statement:
--   Fix S and an identical secondary set T offered after every outcome, including 0. Choose w_l between the minimum and maximum of v_il over S+, and a nonnegative delta such that max_i v_il minus min_i v_il is at most delta for every l in T. The two actual auxiliary maximizations (11)–(12) admit prices with one common markup in each category. Every pair (p^o,r^o) obtained by these maximizations has those common markups and satisfies, for every unrestricted true competing pair (p,r),
--   $$\Pi(S,T,p^o,r^o)\ge e^{-2\delta}\Pi(S,T,p,r).$$
--   Thus the guarantee compares the achieved original-model profit with its unrestricted optimum, not with an auxiliary-model profit. Existence of the construction is part of the conclusion, so an empty argmax cannot make the guarantee vacuous.
--
--   **Formalization Note** Delta is explicitly nonnegative. Without this domain convention, the printed claim fails when T is empty: the spread condition is vacuous and a negative delta requests a factor greater than one. DISPROOF.md gives a one-product optimum of value 1 and delta=-1. For nonempty T the spread hypothesis itself implies delta is nonnegative.
--
--   Differences from the source:
--   - correction: no explicit domain for delta and an empty secondary set is allowed → delta is nonnegative, with all finite S and T still allowed; reason: p. 18 uses delta as a valuation-spread budget; the T=empty, delta=-1 counterexample in DISPROOF.md shows why this boundary repair is necessary and excludes only negative budgets with empty T
--   - encoding: max/min spread and alpha times the optimal true value → pairwise differences on S+ and comparison with every competing price vector; reason: S+ is finite and nonempty and the positive factor preserves the equivalence; this avoids default real suprema
--   - encoding: solve (11) and then (12), calling the resulting policy same-markup/same-markup → assert existence and quantify over all actual auxiliary maximizers, with equal markups in the conclusion; reason: this explicitly realizes the source construction instead of assuming the approximation or selecting a default argmax
-- source:
--   Ke & Wang, Cross-Category Retailing Management: Substitution and Complementarity, accepted manuscript (SSRN 3383023), p. 18, Theorem 3

import Mathlib
import Definitions.Def_CrossSell_Pricing_Supplement_PricingPolicy

namespace CrossSell.Pricing.Supplement

theorem theorem_3 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (S : Finset ι) (T : Finset κ) (u c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (w : κ → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hw : Admissible S T v w) (hspread : Spread S T v δ) :
    (∃ p r, Constructed S T u c s w p r ∧ SameMarkups S T c p s r) ∧
    (∀ p r, Constructed S T u c s w p r →
      SameMarkups S T c p s r ∧ AlphaOptimal S T u c s v p r (Real.exp (-2 * δ))) := by sorry

end CrossSell.Pricing.Supplement

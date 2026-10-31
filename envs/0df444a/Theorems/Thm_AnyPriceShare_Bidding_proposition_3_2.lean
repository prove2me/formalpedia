-- Prove2me | Theorems.Thm_AnyPriceShare_Bidding_proposition_3_2
-- name    : AnyPriceShare.Bidding.proposition_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:18.16498+00:00
-- url     : https://prove2.me/theorems/50b42e30-d5c0-4af9-80dc-ebf7497840aa
-- title:
--   Proposition 3.2, p. 9 — the price form (Definition 1.1) and the packing form (Definition 3.1) of the AnyPrice share coincide
-- statement:
--   Let $w$ be a valuation on bundles of a set of items $S$ that is monotone ($w(T)\le w(T')$ for $T\subseteq T'$) and normalized ($w(\emptyset)=0$), and let $\beta>0$ be an entitlement. Then the AnyPrice share of Definition 3.1 (largest $z$ admitting a distribution over bundles of value at least $z$ in which every item has total weight at most $\beta$) equals the AnyPrice share of Definition 1.1 (minimum over price vectors of total price $1$ of the best affordable bundle):
--
--   $$\mathrm{AnyPrice}^{D}(\beta,w,S)=\mathrm{AnyPrice}(\beta,w,S).$$
--
--   The equivalence lets one bound the APS from above by exhibiting prices and from below by exhibiting a fractional packing; the paper's lower-bound arguments (Lemmas 4.6, 4.7) use the packing form.
--
--   **Formalization Note** Monotonicity and normalization are the paper's standing assumptions on valuations (§2, p. 7); $\beta>0$ is the model's $b_i>0$. The statement is made for every $\beta>0$; for $\beta\ge1$ both sides equal $w(S)$.
-- source:
--   Babaioff, Ezra & Feige, Fair-Share Allocations for Agents with Arbitrary Entitlements, arXiv:2103.04304v4, p. 9, Proposition 3.2 (proof pp. 27–28)

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic

namespace AnyPriceShare.Bidding

/-- Proposition 3.2, p. 9 (proof pp. 27–28): for a monotone, normalized valuation `w` and an
entitlement `β > 0`, the AnyPrice share of Definition 3.1 (packing form) equals that of
Definition 1.1 (price form). -/
theorem proposition_3_2 {m : ℕ} (w : Finset (Fin m) → ℝ) (hmono : Monotone w) (hnorm : w ∅ = 0)
    (β : ℝ) (hβ : 0 < β) (S : Finset (Fin m)) :
    anyPriceDual β w S = anyPrice β w S := by sorry

end AnyPriceShare.Bidding

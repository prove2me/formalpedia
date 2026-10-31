-- Prove2me | Theorems.Thm_AnyPriceShare_Bidding_proposition_3_7_proportional
-- name    : AnyPriceShare.Bidding.proposition_3_7_proportional
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:15.706204+00:00
-- url     : https://prove2.me/theorems/c2170ab0-ff1b-433a-bc91-a69d38aabb6a
-- title:
--   Proposition 3.7 (first inequality), p. 11 — the AnyPrice share is at most the proportional share
-- statement:
--   Let an agent have an additive valuation with non-negative item values $u(j)$ on a set of items $S$, and an entitlement $\beta>0$. Then
--
--   $$\mathrm{Proportional}(\beta,u,S)=\beta\cdot u(S)\ \ge\ \mathrm{AnyPrice}(\beta,u,S).$$
--
--   This is the first of the chain of inequalities of Proposition 3.7; it is the case $k=0$ in the proof of Proposition 4.2 (TPS $\ge$ APS).
--
--   **Formalization Note** Only the first inequality of Proposition 3.7 is formalized; the comparisons with the pessimistic share and the equality and strictness examples are not used by the main theorem.
-- source:
--   Babaioff, Ezra & Feige, Fair-Share Allocations for Agents with Arbitrary Entitlements, arXiv:2103.04304v4, p. 11, Proposition 3.7, first inequality (proof p. 29)

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic

namespace AnyPriceShare.Bidding

/-- Proposition 3.7, p. 11 (first inequality; proof p. 29): for an additive valuation with
non-negative item values `u` and an entitlement `β > 0`,
`Proportional(β, u, S) ≥ AnyPrice(β, u, S)`. -/
theorem proposition_3_7_proportional {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j)
    (β : ℝ) (hβ : 0 < β) (S : Finset (Fin m)) :
    anyPrice β (addVal u) S ≤ proportional β u S := by sorry

end AnyPriceShare.Bidding

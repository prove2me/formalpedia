-- Prove2me | Theorems.Thm_AnyPriceShare_Bidding_proposition_4_2
-- name    : AnyPriceShare.Bidding.proposition_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:20.608594+00:00
-- url     : https://prove2.me/theorems/92813f2e-c476-4088-9e1a-47325131d912
-- title:
--   Proposition 4.2, p. 12 — TPS(b_i, v_i, M) ≥ AnyPrice(b_i, v_i, M) for additive v_i
-- statement:
--   Let an agent have an additive valuation with non-negative item values $u(j)$ on a set of items $S$, and an entitlement $\beta>0$. Then her Truncated Proportional Share is at least her AnyPrice share:
--
--   $$\mathrm{TPS}(\beta,u,S)\ \ge\ \mathrm{AnyPrice}(\beta,u,S).$$
--
--   Together with Lemma D.3 ($\tfrac1{2-b_i}$ of the TPS can be secured in the Bidding Game) this gives the $\tfrac1{2-b_i}$ part of the main theorem.
-- source:
--   Babaioff, Ezra & Feige, Fair-Share Allocations for Agents with Arbitrary Entitlements, arXiv:2103.04304v4, p. 12, Proposition 4.2 (proof pp. 12–13)

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic

namespace AnyPriceShare.Bidding

/-- Proposition 4.2, p. 12 (proof pp. 12–13): for an additive valuation with non-negative item
values `u` and an entitlement `β > 0`, `TPS(β, u, S) ≥ AnyPrice(β, u, S)`. -/
theorem proposition_4_2 {m : ℕ} (u : Fin m → ℝ) (hu : ∀ j, 0 ≤ u j)
    (β : ℝ) (hβ : 0 < β) (S : Finset (Fin m)) :
    anyPrice β (addVal u) S ≤ tps β u S := by sorry

end AnyPriceShare.Bidding

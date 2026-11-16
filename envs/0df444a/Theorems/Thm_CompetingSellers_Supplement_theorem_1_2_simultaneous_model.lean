-- Prove2me | Theorems.Thm_CompetingSellers_Supplement_theorem_1_2_simultaneous_model
-- name    : CompetingSellers.Supplement.theorem_1_2_simultaneous_model
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:32:54.04154+00:00
-- url     : https://prove2.me/theorems/daf17cca-eaa4-4cb7-b049-330f0db2d67e
-- title:
--   Theorem 1.2 (Simultaneous Model) — every pure Nash equilibrium gives both sellers their Bertrand revenues
-- statement:
--   Let $\Sigma$ be an uncountable standard Borel message space with a null message, and let the buyer's values be $a,b>0$ (unit demand, value $\max\{a,b\}$ for both goods). In the **simultaneous model** Alice and Bob choose their (possibly randomized) mechanisms $A$, $B$ at the same time; the buyer then chooses the order of visits and his messages to maximize his expected utility, breaking ties as in the main model, and $\mathrm{rev}_A(A,B)$, $\mathrm{rev}_B(A,B)$ are the sellers' expected revenues. A pair $(A,B)$ is a **pure Nash equilibrium** if neither seller can increase its expected revenue by changing its mechanism:
--   $$\mathrm{rev}_A(A',B)\le\mathrm{rev}_A(A,B)\ \ \forall A',\qquad \mathrm{rev}_B(A,B')\le\mathrm{rev}_B(A,B)\ \ \forall B'.$$
--
--   **Theorem.** Every pure Nash equilibrium $(A,B)$ yields the Bertrand revenues of both sellers:
--   $$\mathrm{rev}_A(A,B)=(a-b)^+,\qquad \mathrm{rev}_B(A,B)=(b-a)^+.$$
--
--   Without commitment, randomized mechanisms give neither seller more than posted-price (Bertrand) competition; in the main model, where Alice commits first, she earns strictly more when $a<C\,b$ (Theorem 1.1).
--
--   **Formalization Note** The sellers' payoffs are the main-model revenues of the base mission (the buyer's behaviour does not depend on the order in which the sellers chose their mechanisms, p.43). The pure Nash equilibrium is the general two-player notion `CompetingChains.Cournot.IsPureNash` with the two revenues as payoffs.
--
--   Differences from the source:
--
--   - encoding: a seller's expected revenue under the buyer's equilibrium play → the published main-model `revenue` (supremum of the expected payment over the buyer's tie-broken selected plans, as a real number); reason: the base mission's convention; the simultaneous model's buyer behaves as in the main model (p.43), so no instance changes
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Theorem 1.2, p.42 (PDF 45); first stated p.5 (PDF 8); pure Nash equilibrium and Bertrand revenues p.41–42 (PDF 44–45)

import Mathlib
import Definitions.Def_CompetingSellers_revenue
import Definitions.Def_CompetingChains_Cournot_TwoPlayerGame

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers.Supplement

/-- **Theorem 1.2 (Simultaneous Model).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Theorem 1.2, p.42 (PDF 45; first stated p.5, PDF 8): "Consider an
instance of the duopoly game in the simultaneous model, in which Alice and Bob select their
randomized mechanisms simultaneously. Then, every pure Nash equilibrium yields the Bertrand revenues
for both sellers." p.41–42 (PDF 44–45): "Recall that `a, b > 0` are the buyer's values … and
`a|b = (a − b)⁺` and `b|a = (b − a)⁺` … A pair `(A, B)` is a pure Nash equilibrium if neither
seller can increase expected revenue by changing mechanisms."

**Formalization Note.** The message space `Σ` is quantified (every uncountable standard Borel `S`
with a null message), as in Theorem 1.1. The buyer's behaviour is the main model's (free order,
`selectedPlans`, p.43: "once the mechanisms are fixed, the buyer's behavior does not depend on the
order in which the sellers chose them"), so the sellers' payoffs are the published `revenue`. A pure
Nash equilibrium is the general two-player notion `IsPureNash` with Alice's and Bob's revenues as
payoffs; there is no leader and no tie-breaking for either seller. -/
theorem theorem_1_2_simultaneous_model (S : Type) [MeasurableSpace S] [StandardBorelSpace S]
    [Uncountable S] (null : S) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∀ A B : Mech S null,
      CompetingChains.Cournot.IsPureNash (fun A' B' => revenue a b A' B' Seller.alice)
        (fun A' B' => revenue a b A' B' Seller.bob) A B →
      revenue a b A B Seller.alice = max (a - b) 0 ∧
        revenue a b A B Seller.bob = max (b - a) 0 := by sorry

end CompetingSellers.Supplement

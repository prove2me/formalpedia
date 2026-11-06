-- Prove2me | Theorems.Thm_CompetingSellers_observation_2_2
-- name    : CompetingSellers.observation_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:57.659548+00:00
-- url     : https://prove2.me/theorems/44715060-76bb-44c1-a524-eb2d597b28cb
-- title:
--   Observation 2.2 (taxation principle) — every mechanism is essentially equivalent to its proper pricing representation
-- statement:
--   Let $\Sigma$ be an uncountable standard Borel message space with null message, and $a,b>0$. For either seller $i$ and every mechanism $M$, the proper pricing representation $P_M$ (built from $M$'s options with payments at most the buyer's value $v_i$ for $i$'s good) is a proper pricing function with $P_M(\bar x)<\infty$; some mechanism realizes it, and every mechanism realizing it is essentially equivalent to $M$.
--
--   Consequently, restricting both sellers to pricing mechanisms preserves their problems:
--
--   1. against every Alice mechanism, Bob's best revenue over all mechanisms equals his best revenue over pricing mechanisms, and a pricing mechanism is a best response among all mechanisms iff it is one among pricing mechanisms;
--   2. every Alice mechanism can be replaced by a pricing mechanism giving both sellers the same revenues against every Bob mechanism, and every Bob mechanism by a pricing mechanism giving both the same revenues against every Alice mechanism.
--
--   This is the bridge from general randomized mechanisms to menus $P:[0,1]\to[0,\infty]$ on which all of §3 works.
--
--   **Formalization Note** The first sentence is stated for the specific representation of the proof (p.54).
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - reading: "every mechanism M … has an essentially equivalent proper pricing mechanism P_M" → the proof's P_M (priceRep v_i M) is proper with P_M(x̄) < ∞, is realized by some mechanism, and every realization is essentially equivalent to M; reason: the paper writes P_M for exactly this representation (p.17: "we will write P_M to denote the essentially equivalent proper pricing mechanism")
--   - reading: "restricting both sellers to such pricing mechanisms preserves their best-response and revenue-optimization problems" → equal optimal values and best responses for Bob over pricing versus all mechanisms, and revenue-preserving pricing replacements for each seller; reason: the meaning of 'preserves the problems': same values, same best responses, same revenues for every opposing mechanism
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Observation 2.2, p.17 (PDF 20); proof pp.54–55 (PDF 57–58)

import Mathlib
import Definitions.Def_CompetingSellers_EssEquiv
import Definitions.Def_CompetingSellers_IsPricingMech
import Definitions.Def_CompetingSellers_priceRep

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Observation 2.2 (Taxation Principle).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Observation 2.2, p.17 (PDF 20; proof p.54): "For a buyer with values `a, b`, every
mechanism `M` offered by either seller has an essentially equivalent proper pricing mechanism
`P_M`. Consequently, restricting both sellers to such pricing mechanisms preserves their
best-response and revenue-optimization problems."

**Formalization Note.** The first sentence is stated for the representation `P_M` built in the
proof (`priceRep v_i M`, `v_i` the buyer's value for seller `i`'s good): it is proper with
`P_M(x̄) < ∞`, some mechanism realizes it, and every realization is essentially equivalent to `M`.
The second sentence is stated as: against every Alice mechanism, Bob's optimal revenue over all
mechanisms equals that over pricing mechanisms and a pricing mechanism is a best response over all
mechanisms iff it is one among pricing mechanisms; and every mechanism of either seller can be
replaced by a pricing mechanism giving both sellers the same revenues against every mechanism of
the other seller. -/
theorem observation_2_2 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∀ (i : Seller) (M : Mech S null),
      IsSellerPricing (priceRep (Plan.valueOf a b i) M) ∧
      (∃ M' : Mech S null, IsPricingMech (priceRep (Plan.valueOf a b i) M) M') ∧
      ∀ M' : Mech S null, IsPricingMech (priceRep (Plan.valueOf a b i) M) M' →
        EssEquiv a b i M M') ∧
    (∀ A : Mech S null,
      (⨆ B : Mech S null, revenue a b A B Seller.bob) =
        (⨆ B : {B : Mech S null // IsPricingMechanism B}, revenue a b A B.1 Seller.bob) ∧
      ∀ B : Mech S null, IsPricingMechanism B →
        ((∀ B' : Mech S null, revenue a b A B' Seller.bob ≤ revenue a b A B Seller.bob) ↔
          ∀ B' : Mech S null, IsPricingMechanism B' →
            revenue a b A B' Seller.bob ≤ revenue a b A B Seller.bob)) ∧
    (∀ A : Mech S null, ∃ A' : Mech S null, IsPricingMechanism A' ∧
      ∀ (B : Mech S null) (i : Seller), revenue a b A' B i = revenue a b A B i) ∧
    ∀ B : Mech S null, ∃ B' : Mech S null, IsPricingMechanism B' ∧
      ∀ (A : Mech S null) (i : Seller), revenue a b A B' i = revenue a b A B i := by sorry

end CompetingSellers

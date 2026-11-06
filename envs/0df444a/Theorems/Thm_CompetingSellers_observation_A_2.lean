-- Prove2me | Theorems.Thm_CompetingSellers_observation_A_2
-- name    : CompetingSellers.observation_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:46.141766+00:00
-- url     : https://prove2.me/theorems/a9187239-e914-424b-a359-f5ab8bf07297
-- title:
--   Observation A.2 — selected buyer plans and Bob's selected best response exist, in the main and the fixed-order models
-- statement:
--   Let $\Sigma$ be an uncountable standard Borel message space with null message and $a,b>0$.
--
--   1. For every pair of mechanisms there is a buyer plan successively maximizing his expected utility, Bob's expected revenue, Alice's expected revenue, the probability of getting Bob's good, the probability of getting Alice's good, and finally preferring the order $AB$.
--   2. For every Alice mechanism $A$, Bob has a best response, and Alice's revenue attains a maximum among Bob's best responses: there is a best response $B$ of Bob to $A$ maximizing $\mathrm{rev}_A(A,\cdot)$ among his best responses.
--
--   3. Both conclusions hold in the aligned and misaligned models, where the buyer must approach a prescribed seller first and his plans are restricted to that order: for each first seller $i$, the successive maximization over plans approaching $i$ first is attained for every pair of mechanisms, and for every Alice mechanism Bob has a best response (for the revenues of this fixed-order selection) maximizing Alice's revenue among his best responses.
--
--   These existence results make the revenues $\mathrm{rev}_A,\mathrm{rev}_B$ and Bob's tie-broken strategy well defined.
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - encoding: the aligned model (buyer must visit Alice first) and the misaligned model (buyer must visit Bob first) → the fixed-order selection selectedPlansFrom a b i with i = alice, i = bob, and its revenues revenueFrom a b i; reason: "buyer plans restricted to the prescribed order" (p.50); the sellers' mechanisms and the buyer's priorities are unchanged, and the order preference is vacuous (footnote 23); same instances
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Observation A.2, p.50 (PDF 53)

import Mathlib
import Definitions.Def_CompetingSellers_IsStackelbergEq

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Observation A.2 (Existence and Tie-Breaking for Bob and the Buyer).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Observation A.2, p.50 (PDF 53): "Suppose the buyer has values `a` and `b`. (i) For every
mechanism pair, there exists a buyer action plan successively maximizing his expected utility,
Bob's expected revenue, Alice's expected revenue, the allocation probability from Bob, and the
allocation probability from Alice, finally preferring AB to BA. (ii) Fix any buyer strategy
selecting plans with the priorities in (i) after every mechanism pair. For every Alice
mechanism, Bob has a best response maximizing his expected revenue, and Alice's expected revenue
attains a maximum among these best responses. Both conclusions hold in the aligned and misaligned
models as well, with buyer plans restricted to the prescribed order."

**Formalization Note.** Revenues under any buyer strategy with these priorities are the `revenue`
values (all selected plans give the same revenues). The aligned and misaligned models are the
fixed-order variants with first seller `i = alice` and `i = bob`: the buyer's selection is
`selectedPlansFrom`, its revenues are `revenueFrom`, and the second part reads: Bob has a best
response under `revenueFrom`, maximizing Alice's `revenueFrom` among his best responses. -/
theorem observation_A_2 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∀ A B : Mech S null, (selectedPlans a b A B).Nonempty) ∧
    (∀ A : Mech S null, ∃ B : Mech S null, IsBobChoice a b A B) ∧
    ∀ i : Seller,
      (∀ A B : Mech S null, (selectedPlansFrom a b i A B).Nonempty) ∧
      ∀ A : Mech S null, ∃ B : Mech S null,
        (∀ B' : Mech S null, revenueFrom a b i A B' Seller.bob ≤ revenueFrom a b i A B Seller.bob) ∧
        ∀ B' : Mech S null,
          (∀ B'' : Mech S null,
            revenueFrom a b i A B'' Seller.bob ≤ revenueFrom a b i A B' Seller.bob) →
          revenueFrom a b i A B' Seller.alice ≤ revenueFrom a b i A B Seller.alice := by sorry

end CompetingSellers

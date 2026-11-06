-- Prove2me | Theorems.Thm_CompetingSellers_lemma_3_5
-- name    : CompetingSellers.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:39.380897+00:00
-- url     : https://prove2.me/theorems/de1a975a-e33b-42eb-8d38-c60ca340e7ed
-- title:
--   Lemma 3.5 — Bob's revenue when the buyer visits him first is at most $x\,p_A(x)$
-- statement:
--   Let $A$ and $B$ be mechanisms of Alice and Bob such that the buyer, facing them, interacts with Bob first. Then there is $x\in[0,1]$ with
--   $$\mathrm{rev}_B(A,B)\le x\cdot p_A(x).$$
--
--   Together with Lemma 3.4 this bounds every Bob-first response by a single lottery.
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - encoding: util_M, z±_M, Aug_M and M(x) of a mechanism through the identification M ≡ P_M (p.18) → mUtil, mZPlus, mZMinus, mAug, priceRep computed from the proof's P_M = priceRep v_i M; reason: the paper's own identification; same instances
--   - encoding: "the buyer … interacts with Bob first" → a selected (tie-broken) plan approaches Bob first; reason: all selected plans share their order (Observation A.5); same instances
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Lemma 3.5, p.21 (PDF 24)

import Mathlib
import Definitions.Def_CompetingSellers_revenue
import Definitions.Def_CompetingSellers_pA

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Lemma 3.5 (Bob-first revenue bound).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Lemma 3.5, p.21 (PDF 24): "Let `A` and `B` be mechanisms for Alice and Bob respectively
such that the buyer, when faced with this pair of mechanisms, interacts with Bob first. Then,
there exists `x ∈ [0, 1]` such that `rev_B(A, B) ≤ x · p_A(x)`."

**Formalization Note.** "Interacts with Bob first": a selected (tie-broken utility-maximizing)
plan approaches Bob first. -/
theorem lemma_3_5 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (A B : Mech S null) (hB : BuyerFirst a b A B Seller.bob) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, revenue a b A B Seller.bob ≤ x * pA a b A x := by sorry

end CompetingSellers

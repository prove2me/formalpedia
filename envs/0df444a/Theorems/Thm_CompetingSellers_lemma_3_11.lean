-- Prove2me | Theorems.Thm_CompetingSellers_lemma_3_11
-- name    : CompetingSellers.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:42.535931+00:00
-- url     : https://prove2.me/theorems/1cb9b1ac-104a-4193-aa9d-bd21535fefb7
-- title:
--   Lemma 3.11 ($a\ge b$) — upper bound on Alice's revenue in terms of Bob's
-- statement:
--   Let $a\ge b$, let $A,B$ be any mechanisms of Alice and Bob, and $R=\mathrm{rev}_B(A,B)$. Then
--   $$\mathrm{rev}_A(A,B)\le a\Big(1-\frac Rb\Big)-\mathrm{util}_A(a).$$
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - encoding: util_M, z±_M, Aug_M and M(x) of a mechanism through the identification M ≡ P_M (p.18) → mUtil, mZPlus, mZMinus, mAug, priceRep computed from the proof's P_M = priceRep v_i M; reason: the paper's own identification; same instances
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Lemma 3.11, p.25 (PDF 28)

import Mathlib
import Definitions.Def_CompetingSellers_revenue
import Definitions.Def_CompetingSellers_priceRep

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Lemma 3.11 (`a ≥ b`: upper bound on Alice's revenue).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Lemma 3.11, p.25 (PDF 28): "Let `a ≥ b`. Let `A` and `B` be an arbitrary pair of
mechanisms for Alice and Bob respectively and let `R = rev_B(A, B)`. We have:
`rev_A(A, B) ≤ a · (1 − R/b) − util_A(a)`."
 -/
theorem lemma_3_11 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (A B : Mech S null) :
    revenue a b A B Seller.alice ≤ a * (1 - revenue a b A B Seller.bob / b) - mUtil a A a := by sorry

end CompetingSellers

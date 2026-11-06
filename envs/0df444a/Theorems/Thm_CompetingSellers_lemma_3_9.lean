-- Prove2me | Theorems.Thm_CompetingSellers_lemma_3_9
-- name    : CompetingSellers.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:14.624198+00:00
-- url     : https://prove2.me/theorems/87a3cd75-b051-4023-9c7b-7d67ecb6f9ff
-- title:
--   Lemma 3.9 — Alice-first responses are dominated by a double lottery
-- statement:
--   Let $A,B$ be mechanisms of Alice and Bob such that the buyer interacts with Alice first, and let $q=b-a+a|_B$ with $a|_B=a-\mathrm{Aug}_B(a,b)$. Then $q\in[b|_a,b]$ and
--   $$\mathrm{rev}_B(A,B)\le\mathrm{rev}_B\big(A,\mathrm{DL}_{x_A(q),q}\big)$$
--   for every Bob mechanism realizing $\mathrm{DL}_{x_A(q),q}$.
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - encoding: util_M, z±_M, Aug_M and M(x) of a mechanism through the identification M ≡ P_M (p.18) → mUtil, mZPlus, mZMinus, mAug, priceRep computed from the proof's P_M = priceRep v_i M; reason: the paper's own identification; same instances
--   - encoding: SL_{x,p}, DL_{x,q}, FP(p), Ã used as mechanisms → any mechanism realizing the pricing function (IsPricingMech); reason: all realizations have the same image and therefore the same play; the paper implements pricing functions this way (p.54)
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Lemma 3.9, p.23 (PDF 26)

import Mathlib
import Definitions.Def_CompetingSellers_revenue
import Definitions.Def_CompetingSellers_IsPricingMech
import Definitions.Def_CompetingSellers_sl
import Definitions.Def_CompetingSellers_pA

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Lemma 3.9 (Alice-first revenue bound).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Lemma 3.9, p.23 (PDF 26): "Let `A` and `B` be mechanisms for Alice and Bob respectively
such that the buyer, when faced with this pair of mechanisms, interacts with Alice first. Then,
for `q = b − a + a|_B ∈ [b|_a, b]`, we have that `rev_B(A, B) ≤ rev_B(A, DL_{x_A(q),q})`."

**Formalization Note.** `a|_B = a − Aug_B(a, b)` (Lemma 3.1) with `Aug_B` of `P_B`; the membership
`q ∈ [b|_a, b]` is part of the conclusion; `DL_{x_A(q),q}` is any mechanism realizing it. -/
theorem lemma_3_9 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (A B : Mech S null) (hA : BuyerFirst a b A B Seller.alice) :
    (b - a + (a - mAug b B a b)) ∈ Set.Icc (max 0 (b - a)) b ∧
    ∀ D : Mech S null,
      IsPricingMech (dl a b (xA a b A (b - a + (a - mAug b B a b))) (b - a + (a - mAug b B a b))) D →
        revenue a b A B Seller.bob ≤ revenue a b A D Seller.bob := by sorry

end CompetingSellers

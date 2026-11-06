-- Prove2me | Theorems.Thm_CompetingSellers_lemma_3_4
-- name    : CompetingSellers.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:21.483798+00:00
-- url     : https://prove2.me/theorems/a47e2827-8e7f-4671-ab82-8b612cd45406
-- title:
--   Lemma 3.4 — the Bob-first threshold price $p_A(x)$
-- statement:
--   Let $A$ be Alice's mechanism and $x\in[0,1]$. For every $p\in[b|_a,\,b-\mathrm{Aug}_A(b,a)]$ and every Bob mechanism realizing the single lottery $\mathrm{SL}_{x,p}$,
--   $$p\le p_A(x)\iff \mathrm{util}_{AB}(A,\mathrm{SL}_{x,p})\le\mathrm{util}_{BA}(A,\mathrm{SL}_{x,p}).$$
--   If moreover $\mathrm{util}_A(a)>0$ and $0<x<1$, then for the same $p$,
--   $$p<p_A(x)\iff \mathrm{util}_{AB}(A,\mathrm{SL}_{x,p})<\mathrm{util}_{BA}(A,\mathrm{SL}_{x,p}).$$
--
--   It identifies the highest per-unit price at which Bob's single lottery still draws the buyer to him first.
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - encoding: util_M, z±_M, Aug_M and M(x) of a mechanism through the identification M ≡ P_M (p.18) → mUtil, mZPlus, mZMinus, mAug, priceRep computed from the proof's P_M = priceRep v_i M; reason: the paper's own identification; same instances
--   - encoding: SL_{x,p}, DL_{x,q}, FP(p), Ã used as mechanisms → any mechanism realizing the pricing function (IsPricingMech); reason: all realizations have the same image and therefore the same play; the paper implements pricing functions this way (p.54)
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Lemma 3.4, p.21 (PDF 24)

import Mathlib
import Definitions.Def_CompetingSellers_revenue
import Definitions.Def_CompetingSellers_IsPricingMech
import Definitions.Def_CompetingSellers_sl
import Definitions.Def_CompetingSellers_pA

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Lemma 3.4 (Bob-first threshold price).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Lemma 3.4, p.21 (PDF 24): "Let `A` be a mechanism for Alice and `x ∈ [0, 1]`. For all
`p ∈ [b|_a, b − Aug_A(b, a)]`, it holds that: `p ≤ p_A(x) ⟺ util_AB(A, SL_{x,p}) ≤
util_BA(A, SL_{x,p})`. Moreover, if we have `util_A(a) > 0` and `0 < x < 1`, then, for all
`p ∈ [b|_a, b − Aug_A(b, a)]`, it holds that: `p < p_A(x) ⟺ util_AB(A, SL_{x,p}) <
util_BA(A, SL_{x,p})`."

**Formalization Note.** `SL_{x,p}` enters as any Bob mechanism realizing the pricing function
`sl x p`; `util_AB`, `util_BA` are `orderUtil … alice`, `orderUtil … bob`; `b|_a = max(0, b − a)`. -/
theorem lemma_3_4 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (A : Mech S null) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∀ p ∈ Set.Icc (max 0 (b - a)) (b - mAug a A b a), ∀ B : Mech S null,
      IsPricingMech (sl x p) B →
        (p ≤ pA a b A x ↔ orderUtil a b A B Seller.alice ≤ orderUtil a b A B Seller.bob)) ∧
    (0 < mUtil a A a → 0 < x → x < 1 →
      ∀ p ∈ Set.Icc (max 0 (b - a)) (b - mAug a A b a), ∀ B : Mech S null,
        IsPricingMech (sl x p) B →
          (p < pA a b A x ↔ orderUtil a b A B Seller.alice < orderUtil a b A B Seller.bob)) := by sorry

end CompetingSellers

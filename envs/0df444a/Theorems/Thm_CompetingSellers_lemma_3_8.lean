-- Prove2me | Theorems.Thm_CompetingSellers_lemma_3_8
-- name    : CompetingSellers.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:39.610375+00:00
-- url     : https://prove2.me/theorems/f8bfd442-1b3c-4366-9b2d-fd99b395566a
-- title:
--   Lemma 3.8 — the Alice-first threshold $x_A(q)$ and Bob's double-lottery revenue
-- statement:
--   Let $A$ be Alice's mechanism, $\Delta=|a-b|$ and $q\in[b|_a,b]$. For every $x\in\big[0,\frac{b-q}{b-b|_a}\big]$ and every Bob mechanism realizing $\mathrm{DL}_{x,q}$,
--   $$x\le x_A(q)\iff \mathrm{util}_{BA}(A,\mathrm{DL}_{x,q})\le\mathrm{util}_{AB}(A,\mathrm{DL}_{x,q}).$$
--   Moreover:
--
--   1. if $a\ge b$, then for all $x\in[0,x_A(q)]$, $\mathrm{rev}_B(A,\mathrm{DL}_{x,q})=q\,\big(1-z^-_A(\Delta+q)\big)$;
--   2. if $a\le b$, then $\mathrm{rev}_B(A,\mathrm{DL}_{x_A(q),q})=q-z^-_A(q-\Delta)\,\big(q-\Delta\,x_A(q)\big)$.
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - encoding: util_M, z±_M, Aug_M and M(x) of a mechanism through the identification M ≡ P_M (p.18) → mUtil, mZPlus, mZMinus, mAug, priceRep computed from the proof's P_M = priceRep v_i M; reason: the paper's own identification; same instances
--   - encoding: SL_{x,p}, DL_{x,q}, FP(p), Ã used as mechanisms → any mechanism realizing the pricing function (IsPricingMech); reason: all realizations have the same image and therefore the same play; the paper implements pricing functions this way (p.54)
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Lemma 3.8, p.23 (PDF 26)

import Mathlib
import Definitions.Def_CompetingSellers_revenue
import Definitions.Def_CompetingSellers_IsPricingMech
import Definitions.Def_CompetingSellers_sl
import Definitions.Def_CompetingSellers_pA

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Lemma 3.8 (Alice-first threshold and Bob's double-lottery revenue).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Lemma 3.8, p.23 (PDF 26): "Let `A` be a mechanism for Alice and `q ∈ [b|_a, b]`. For all
`x ∈ [0, (b − q)/(b − b|_a)]`, we have: `x ≤ x_A(q) ⟺ util_BA(A, DL_{x,q}) ≤
util_AB(A, DL_{x,q})`. Moreover, the following hold: 1. If `a ≥ b`, for all `x ∈ [0, x_A(q)]`,
we have `rev_B(A, DL_{x,q}) = q · (1 − z⁻_A(∆ + q))`. 2. If `a ≤ b`, we have
`rev_B(A, DL_{x_A(q),q}) = q − z⁻_A(q − ∆) · (q − ∆ · x_A(q))`."

**Formalization Note.** `DL_{x,q}` enters as any Bob mechanism realizing `dl a b x q`;
`∆ = |a − b|`; `z⁻_A` is that of `P_A`. -/
theorem lemma_3_8 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (A : Mech S null) (q : ℝ) (hq : q ∈ Set.Icc (max 0 (b - a)) b) :
    (∀ x ∈ Set.Icc (0 : ℝ) ((b - q) / (b - max 0 (b - a))), ∀ B : Mech S null,
      IsPricingMech (dl a b x q) B →
        (x ≤ xA a b A q ↔ orderUtil a b A B Seller.bob ≤ orderUtil a b A B Seller.alice)) ∧
    (b ≤ a → ∀ x ∈ Set.Icc (0 : ℝ) (xA a b A q), ∀ B : Mech S null,
      IsPricingMech (dl a b x q) B →
        revenue a b A B Seller.bob = q * (1 - mZMinus a A (|a - b| + q))) ∧
    (a ≤ b → ∀ B : Mech S null, IsPricingMech (dl a b (xA a b A q) q) B →
      revenue a b A B Seller.bob =
        q - mZMinus a A (q - |a - b|) * (q - |a - b| * xA a b A q)) := by sorry

end CompetingSellers

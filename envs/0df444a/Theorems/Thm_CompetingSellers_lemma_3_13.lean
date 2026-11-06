-- Prove2me | Theorems.Thm_CompetingSellers_lemma_3_13
-- name    : CompetingSellers.lemma_3_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:17.250975+00:00
-- url     : https://prove2.me/theorems/663351af-c423-4150-97ec-7af20a5a6b86
-- title:
--   Lemma 3.13 — the Large-Alice equalizer caps Bob at $R$ and gives Alice the bound (4)
-- statement:
--   Let $a\ge b$, $R\in[0,b]$, $s=s(R)$ the root of (3), and $A=A^{LA}_R$. For every Bob mechanism $B$ and every mechanism $F$ realizing $\mathrm{FP}(b)$,
--   $$\mathrm{rev}_B(A,B)\le\mathrm{rev}_B(A,F)=R.$$
--   Moreover, if $B$ is the best response picked by Bob,
--   $$\mathrm{rev}_A(A,B)=a\Big(1-\frac Rb\Big)-\mathrm{util}_A(a)=a\Big(1-\frac Rb\Big)-b\Big(1-\frac{R}{s-\Delta}\Big).$$
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - encoding: util_M, z±_M, Aug_M and M(x) of a mechanism through the identification M ≡ P_M (p.18) → mUtil, mZPlus, mZMinus, mAug, priceRep computed from the proof's P_M = priceRep v_i M; reason: the paper's own identification; same instances
--   - encoding: SL_{x,p}, DL_{x,q}, FP(p), Ã used as mechanisms → any mechanism realizing the pricing function (IsPricingMech); reason: all realizations have the same image and therefore the same play; the paper implements pricing functions this way (p.54)
--   - encoding: "the best-response picked by Bob" → IsBobChoice: a best response maximizing Alice's revenue among Bob's best responses; reason: Bob's tie-breaking rule of p.16; same instances
--   - encoding: A^{LA}_R "the mechanism with the following allocation rule" for the s of eq. (3) → any mechanism A with IsLargeAliceEq a b R s A (z⁺_A equal to the rule, s a root of (3)); reason: the equalizer is determined by its allocation rule up to essential equivalence (Lemma 2.3)
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Lemma 3.13, p.25 (PDF 28)

import Mathlib
import Definitions.Def_CompetingSellers_IsStackelbergEq
import Definitions.Def_CompetingSellers_IsPricingMech
import Definitions.Def_CompetingSellers_sl
import Definitions.Def_CompetingSellers_IsLargeAliceEq

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Lemma 3.13 (Large-Alice equalizer).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Lemma 3.13, p.25 (PDF 28): "Let `a ≥ b` and `R ∈ [0, b]`. For all mechanisms `B` for Bob,
it holds that `rev_B(A^{LA}_R, B) ≤ rev_B(A^{LA}_R, FP(b)) = R`. Moreover, when `B` is the
best-response picked by Bob, we have `rev_A(A^{LA}_R, B) = a · (1 − R/b) − util_{A^{LA}_R}(a)
= a · (1 − R/b) − b · (1 − R/(s − ∆))`."

**Formalization Note.** `A^{LA}_R` is any mechanism with the allocation rule of Definition 3.12
for the root `s` of eq. (3) (`IsLargeAliceEq`, which includes `R ∈ [0, b]`); `FP(b)` is any
mechanism realizing `fp b`; "the best-response picked by Bob" is `IsBobChoice`. -/
theorem lemma_3_13 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (R s : ℝ) (A : Mech S null)
    (hA : IsLargeAliceEq a b R s A) :
    (∀ F : Mech S null, IsPricingMech (fp b) F →
      (∀ B : Mech S null, revenue a b A B Seller.bob ≤ revenue a b A F Seller.bob) ∧
        revenue a b A F Seller.bob = R) ∧
    ∀ B : Mech S null, IsBobChoice a b A B →
      revenue a b A B Seller.alice = a * (1 - R / b) - mUtil a A a ∧
        revenue a b A B Seller.alice = a * (1 - R / b) - b * (1 - R / (s - |a - b|)) := by sorry

end CompetingSellers

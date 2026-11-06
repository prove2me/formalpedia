-- Prove2me | Theorems.Thm_CompetingSellers_lemma_3_18
-- name    : CompetingSellers.lemma_3_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:29.672621+00:00
-- url     : https://prove2.me/theorems/e1c538ee-2a9d-4a4f-aeeb-725b9f0b9c44
-- title:
--   Lemma 3.18 — the Large-Bob equalizer caps Bob at $R$ and gives Alice $ax-bu$
-- statement:
--   Let $a<b$, $\Delta=b-a$, $R\in(\Delta,b]$, $x=1-R/b$, $u=u(x)$ (or $0$ if $x=0$), and $A=A^{LB}_R$. For every Bob mechanism $B$ and every mechanism $F$ realizing $\mathrm{FP}(b)$,
--   $$\mathrm{rev}_B(A,B)\le\mathrm{rev}_B(A,F)=R.$$
--   Moreover, if $B$ is the best response picked by Bob, $\mathrm{rev}_A(A,B)=ax-bu$.
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - encoding: util_M, z±_M, Aug_M and M(x) of a mechanism through the identification M ≡ P_M (p.18) → mUtil, mZPlus, mZMinus, mAug, priceRep computed from the proof's P_M = priceRep v_i M; reason: the paper's own identification; same instances
--   - encoding: SL_{x,p}, DL_{x,q}, FP(p), Ã used as mechanisms → any mechanism realizing the pricing function (IsPricingMech); reason: all realizations have the same image and therefore the same play; the paper implements pricing functions this way (p.54)
--   - encoding: "the best-response picked by Bob" → IsBobChoice: a best response maximizing Alice's revenue among Bob's best responses; reason: Bob's tie-breaking rule of p.16; same instances
--   - encoding: A^{LB}_R "the mechanism with the following allocation rule" for u = u(x) → any mechanism A with IsLargeBobEq a b R u A; reason: the equalizer is determined by its allocation rule up to essential equivalence (Lemma 2.3)
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Lemma 3.18, p.29 (PDF 32)

import Mathlib
import Definitions.Def_CompetingSellers_IsStackelbergEq
import Definitions.Def_CompetingSellers_IsPricingMech
import Definitions.Def_CompetingSellers_sl
import Definitions.Def_CompetingSellers_IsLargeBobEq

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Lemma 3.18 (Large-Bob equalizer).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Lemma 3.18, p.29 (PDF 32): "Let `a < b` and `R ∈ (∆, b]`. For all mechanisms `B` for Bob,
we have `rev_B(A^{LB}_R, B) ≤ rev_B(A^{LB}_R, FP(b)) = R`. Moreover, when `B` is the
best-response picked by Bob, we have `rev_A(A^{LB}_R, B) = ax − bu`, where `x = 1 − R/b`."

**Formalization Note.** `A^{LB}_R` is any mechanism with the allocation rule of Definition 3.17
for `u = u(x)` (`IsLargeBobEq`, which includes `R ∈ (∆, b]`); `FP(b)` any mechanism realizing
`fp b`; "the best-response picked by Bob" is `IsBobChoice`. -/
theorem lemma_3_18 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (R u : ℝ) (A : Mech S null)
    (hA : IsLargeBobEq a b R u A) :
    (∀ F : Mech S null, IsPricingMech (fp b) F →
      (∀ B : Mech S null, revenue a b A B Seller.bob ≤ revenue a b A F Seller.bob) ∧
        revenue a b A F Seller.bob = R) ∧
    ∀ B : Mech S null, IsBobChoice a b A B →
      revenue a b A B Seller.alice = a * (1 - R / b) - b * u := by sorry

end CompetingSellers

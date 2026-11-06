-- Prove2me | Theorems.Thm_CompetingSellers_lemma_3_16
-- name    : CompetingSellers.lemma_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:04.716616+00:00
-- url     : https://prove2.me/theorems/2af827eb-096b-4713-8128-e3b61077050d
-- title:
--   Lemma 3.16 ($a<b$) — capping Alice's mechanism at the buyer's option
-- statement:
--   Let $a<b$, $\Delta=b-a$. Let $B$ be a best response of Bob to Alice's mechanism $A$, let a selected plan for $(A,B)$ visit Alice first and take from her an option with allocation probability $x$, let $R=\mathrm{rev}_B(A,B)>\Delta$, and let $\tilde A$ realize $A$ capped at $x$ ($\tilde A(z)=A(z)$ for $z\le x$, $\infty$ above). Then for every Bob mechanism $\tilde B$ and every mechanism realizing $\mathrm{DL}_{0,b}$,
--   $$\mathrm{rev}_B(\tilde A,\tilde B)\le\mathrm{rev}_B(\tilde A,\mathrm{DL}_{0,b})=b(1-x),\qquad \mathrm{rev}_A(\tilde A,\mathrm{DL}_{0,b})=ax-\mathrm{util}_{\tilde A}(a).$$
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - encoding: util_M, z±_M, Aug_M and M(x) of a mechanism through the identification M ≡ P_M (p.18) → mUtil, mZPlus, mZMinus, mAug, priceRep computed from the proof's P_M = priceRep v_i M; reason: the paper's own identification; same instances
--   - encoding: SL_{x,p}, DL_{x,q}, FP(p), Ã used as mechanisms → any mechanism realizing the pricing function (IsPricingMech); reason: all realizations have the same image and therefore the same play; the paper implements pricing functions this way (p.54)
--   - reading: the lemma's sentence without the case hypothesis; §3.3.2 assumes a < b throughout → hypothesis a < b; reason: the section's standing assumption, under which Δ = b − a
--   - reading: "Let A, B, R, and x be as above" → explicit hypotheses: B is a best response to A, a selected plan π visits Alice first with first allocation x, R = rev_B(A, B), and Ã realizes cap(P_A, x); reason: the context stated in the sentence before the lemma (p.28) and eq. (6)
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Lemma 3.16, p.28 (PDF 31), context pp.27–28

import Mathlib
import Definitions.Def_CompetingSellers_IsStackelbergEq
import Definitions.Def_CompetingSellers_IsPricingMech
import Definitions.Def_CompetingSellers_sl
import Definitions.Def_CompetingSellers_priceRep

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Lemma 3.16 (capping Alice's mechanism).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Lemma 3.16, p.28 (PDF 31), with the context of pp.27–28: "fix `A` and a best response `B`
yielding Bob revenue `R`"; "if `B` best responds to `A` and the buyer goes to Alice first and gets
the item with probability `x`"; eq. (6): "`Ã(z) = A(z)` if `0 ≤ z ≤ x`, `∞` if `x < z ≤ 1`".
"Lemma 3.16. Let `A, B, R`, and `x` be as above and assume that `R > ∆`. For all mechanisms `B̃`
for Bob, it holds that `rev_B(Ã, B̃) ≤ rev_B(Ã, DL_{0,b}) = b · (1 − x)`. Moreover, we have
`rev_A(Ã, DL_{0,b}) = ax − util_Ã(a)`."

**Formalization Note.** Standing `a < b` (§3.3.2). "As above": `B` is a best response to `A`, a
selected plan `π` visits Alice first and takes from her an option with allocation probability
`x`, and `R = rev_B(A, B)`. `Ã` is any mechanism realizing the cap at `x` of `P_A`;
`DL_{0,b}` any mechanism realizing `dl a b 0 b`. -/
theorem lemma_3_16 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (A B : Mech S null) (hB : IsBestResponse a b A B)
    (π : Plan S) (hπ : π ∈ selectedPlans a b A B) (hfirst : π.first = Seller.alice)
    (x : ℝ) (hx : π.firstAlloc A B = x) (R : ℝ) (hR : revenue a b A B Seller.bob = R)
    (hRΔ : |a - b| < R) (At : Mech S null) (hAt : IsPricingMech (cap (priceRep a A) x) At) :
    ∀ D : Mech S null, IsPricingMech (dl a b 0 b) D →
      (∀ Bt : Mech S null, revenue a b At Bt Seller.bob ≤ revenue a b At D Seller.bob) ∧
      revenue a b At D Seller.bob = b * (1 - x) ∧
      revenue a b At D Seller.alice = a * x - mUtil a At a := by sorry

end CompetingSellers

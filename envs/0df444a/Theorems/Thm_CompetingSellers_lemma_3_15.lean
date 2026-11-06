-- Prove2me | Theorems.Thm_CompetingSellers_lemma_3_15
-- name    : CompetingSellers.lemma_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:47.788188+00:00
-- url     : https://prove2.me/theorems/7f574e0b-6ba1-4f18-ada5-b5a4d2e3350d
-- title:
--   Lemma 3.15 ($a<b$) — Alice's revenue against $\mathrm{FP}(b)=\mathrm{DL}_{0,b}$
-- statement:
--   Let $a<b$, let $A$ be Alice's mechanism and let Bob use a mechanism realizing $\mathrm{DL}_{0,b}$ (that is, $\mathrm{FP}(b)$), with $R=\mathrm{rev}_B(A,\mathrm{DL}_{0,b})$. Then
--   $$\mathrm{rev}_A(A,\mathrm{DL}_{0,b})=a\Big(1-\frac Rb\Big)-\mathrm{util}_A(a).$$
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - encoding: util_M, z±_M, Aug_M and M(x) of a mechanism through the identification M ≡ P_M (p.18) → mUtil, mZPlus, mZMinus, mAug, priceRep computed from the proof's P_M = priceRep v_i M; reason: the paper's own identification; same instances
--   - encoding: SL_{x,p}, DL_{x,q}, FP(p), Ã used as mechanisms → any mechanism realizing the pricing function (IsPricingMech); reason: all realizations have the same image and therefore the same play; the paper implements pricing functions this way (p.54)
--   - reading: the lemma's sentence without the case hypothesis; §3.3.2 assumes a < b throughout → hypothesis a < b; reason: the section's standing assumption, under which Δ = b − a
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Lemma 3.15, p.27 (PDF 30), §3.3.2

import Mathlib
import Definitions.Def_CompetingSellers_revenue
import Definitions.Def_CompetingSellers_IsPricingMech
import Definitions.Def_CompetingSellers_sl
import Definitions.Def_CompetingSellers_priceRep

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Lemma 3.15 (`a < b`: Alice's revenue against `FP(b) = DL_{0,b}`).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Lemma 3.15, p.27 (PDF 30): "Let `A` be a mechanism for Alice and let
`R = rev_B(A, DL_{0,b})`. We have: `rev_A(A, DL_{0,b}) = a · (1 − R/b) − util_A(a)`."

**Formalization Note.** Standing `a < b` (§3.3.2). `DL_{0,b}` is any Bob mechanism realizing
`dl a b 0 b` (= `FP(b)` on `[0, 1]`). -/
theorem lemma_3_15 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (A D : Mech S null) (hD : IsPricingMech (dl a b 0 b) D) :
    revenue a b A D Seller.alice = a * (1 - revenue a b A D Seller.bob / b) - mUtil a A a := by sorry

end CompetingSellers

-- Prove2me | Theorems.Thm_CompetingSellers_lemma_3_10
-- name    : CompetingSellers.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:34.75848+00:00
-- url     : https://prove2.me/theorems/d4361692-4331-407c-a882-c9016e6507a8
-- title:
--   Lemma 3.10 ($a\ge b$) — lower bound on Alice's monopolist utility
-- statement:
--   Let $a\ge b$, $\Delta=a-b$, $R>0$, and let $A$ be Alice's mechanism with $\mathrm{util}_A(a)>0$ such that $\mathrm{rev}_B(A,B)\le R$ for every Bob mechanism $B$. Then for all $x\in[R/b,1]$,
--   $$\mathrm{util}_A(a)\ \ge\ \frac1x\int_{R+\Delta+b(1-x)}^{a}\Big(1-\frac{R}{v-\Delta}\Big)\,dv.$$
--
--   If Bob can earn at most $R$, Alice must leave the buyer a large utility.
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - encoding: util_M, z±_M, Aug_M and M(x) of a mechanism through the identification M ≡ P_M (p.18) → mUtil, mZPlus, mZMinus, mAug, priceRep computed from the proof's P_M = priceRep v_i M; reason: the paper's own identification; same instances
--   - reading: the lemma's sentence without the case hypothesis; §3.3.1 assumes a ≥ b throughout → hypothesis b ≤ a; reason: the section's standing assumption, under which Δ = a − b
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Lemma 3.10, p.24 (PDF 27), §3.3.1

import Mathlib
import Definitions.Def_CompetingSellers_revenue
import Definitions.Def_CompetingSellers_priceRep

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Lemma 3.10 (`a ≥ b`: lower bound on Alice's monopolist utility).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Lemma 3.10, p.24 (PDF 27), §3.3.1 "When `a ≥ b`": "Let `R > 0` and `A` be a mechanism for
Alice such that `util_A(a) > 0` and for all mechanisms `B` for Bob, we have `rev_B(A, B) ≤ R`.
For all `x ∈ [R/b, 1]`, we have: `util_A(a) ≥ (1/x) · ∫_{R+∆+b·(1−x)}^a (1 − R/(v − ∆)) dv`."

**Formalization Note.** `a ≥ b` is the standing assumption of §3.3.1 (so `∆ = a − b`). The
integrand is continuous on the range of integration (`v − ∆ ≥ R > 0`). -/
theorem lemma_3_10 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (R : ℝ) (hR : 0 < R) (A : Mech S null)
    (hu : 0 < mUtil a A a) (hrev : ∀ B : Mech S null, revenue a b A B Seller.bob ≤ R)
    (x : ℝ) (hx : x ∈ Set.Icc (R / b) 1) :
    (1 / x) * ∫ v in (R + |a - b| + b * (1 - x))..a, (1 - R / (v - |a - b|)) ≤ mUtil a A a := by sorry

end CompetingSellers

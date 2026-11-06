-- Prove2me | Theorems.Thm_CompetingSellers_lemma_3_14
-- name    : CompetingSellers.lemma_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:58.521617+00:00
-- url     : https://prove2.me/theorems/f30e93e1-6a11-476a-863e-daf77c6e8a27
-- title:
--   Lemma 3.14 ($a<b$) — utility and allocation lower bounds from Bob's revenue cap
-- statement:
--   Let $a<b$, $\Delta=b-a$, $R\ge\Delta$, and let $A$ be Alice's mechanism with $0<\mathrm{util}_A(a)<a$ such that $\mathrm{rev}_B(A,B)\le R$ for every Bob mechanism $B$.
--
--   1. For all $v\in[R-\Delta,a]$: $\mathrm{util}_A(v)\ge\frac{v+\Delta-R}{b}\,\mathrm{util}_A(a)$.
--   2. For all $v\in(0,a]$:
--   $$z^-_A(v)\ \ge\ \frac{v+\Delta-R}{v+\Delta-\Delta\,x_A(v+\Delta)}=\frac{v+\Delta-R}{v+\Delta\,\frac{v-\mathrm{util}_A(v)}{a-\mathrm{util}_A(a)}}.$$
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - encoding: util_M, z±_M, Aug_M and M(x) of a mechanism through the identification M ≡ P_M (p.18) → mUtil, mZPlus, mZMinus, mAug, priceRep computed from the proof's P_M = priceRep v_i M; reason: the paper's own identification; same instances
--   - reading: the lemma's sentence without the case hypothesis; §3.3.2 assumes a < b throughout → hypothesis a < b; reason: the section's standing assumption, under which Δ = b − a
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Lemma 3.14, p.27 (PDF 30), §3.3.2

import Mathlib
import Definitions.Def_CompetingSellers_revenue
import Definitions.Def_CompetingSellers_pA

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Lemma 3.14 (`a < b`: utility and allocation lower bounds).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), Lemma 3.14, p.27 (PDF 30), §3.3.2 "When `a < b`": "Let `R ≥ ∆` and `A` be a mechanism for
Alice such that `0 < util_A(a) < a` and for all mechanisms `B` for Bob, we have `rev_B(A, B) ≤ R`.
1. For all `v ∈ [R − ∆, a]`, we have: `util_A(v) ≥ ((v + ∆ − R)/b) · util_A(a)`.
2. For all `v ∈ (0, a]`, we have: `z⁻_A(v) ≥ (v + ∆ − R)/(v + ∆ − ∆ · x_A(v + ∆)) =
(v + ∆ − R)/(v + ∆ · (v − util_A(v))/(a − util_A(a)))`."

**Formalization Note.** `a < b` is the standing assumption of §3.3.2 (so `∆ = b − a`). -/
theorem lemma_3_14 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (R : ℝ) (hR : |a - b| ≤ R) (A : Mech S null)
    (hu : 0 < mUtil a A a ∧ mUtil a A a < a)
    (hrev : ∀ B : Mech S null, revenue a b A B Seller.bob ≤ R) :
    (∀ v ∈ Set.Icc (R - |a - b|) a, (v + |a - b| - R) / b * mUtil a A a ≤ mUtil a A v) ∧
    ∀ v ∈ Set.Ioc (0 : ℝ) a,
      (v + |a - b| - R) / (v + |a - b| - |a - b| * xA a b A (v + |a - b|)) ≤ mZMinus a A v ∧
      (v + |a - b| - R) / (v + |a - b| - |a - b| * xA a b A (v + |a - b|)) =
        (v + |a - b| - R) / (v + |a - b| * ((v - mUtil a A v) / (a - mUtil a A a))) := by sorry

end CompetingSellers

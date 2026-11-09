-- Prove2me | Theorems.Thm_FacilityIncompatibilities_UniformMatroid_lemma_12
-- name    : FacilityIncompatibilities.UniformMatroid.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:25.884305+00:00
-- url     : https://prove2.me/theorems/d7ed0b6b-ee75-4357-bca8-f0a88937204b
-- title:
--   Lemma 12 — a minimum-cost injection O → S fixing S ∩ O
-- statement:
--   Let $d$ be the (pseudo)metric of an FL-MI instance and let $O,S\subseteq V_F$ with $|O|<|S|$. There exists a minimum-cost injection $\mu:O\to S$, i.e. one minimizing $\sum_{o\in O}d(o,\mu(o))$ over all injections $O\to S$, such that
--
--   $$\mu(i)=i\qquad\text{for every } i\in S\cap O.$$
--
--   This is the injection used to tie-break the assignment $\pi$ in §2.1.
--
--   Differences from the source:
--   - generalization: metric distances d on V_C ∪ V_F (Definition 1) → a pseudometric: d(x,x)=0, symmetry and the triangle inequality, distinct points may be at distance 0; reason: every metric satisfies these axioms, so every instance of the source is covered
--   - generalization: O, S the fixed globally optimal and locally optimal solutions of §2.1 → any finite facility sets O, S with |O| < |S|; reason: the statement and proof use only |O| < |S| and the metric; the §2.1 sets are a special case
--   - reading: “µ(i) = i for every q ∈ S ∩ O” (bound variable printed as q) → ∀ i ∈ S ∩ O, μ i = i; reason: §2.1 (printed p.5) and the proof state µ(i) = i for each i ∈ O ∩ S; the q is a typo
--   - encoding: an injection μ : O → S → a function μ : F → F with μ(O) ⊆ S and injective on O; values off O are irrelevant; reason: Lean convention; the same injections
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Lemma 12, printed p.10 / PDF p.11

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Compression

namespace FacilityIncompatibilities.UniformMatroid

/-- **Lemma 12** (printed p.10 / PDF p.11): if `|O| < |S|`, there is a minimum-cost injection
`μ : O → S` with `μ(i) = i` for every `i ∈ S ∩ O`. -/
theorem lemma_12 {C F : Type*} [DecidableEq F] (I : Instance C F) (hI : I.Valid)
    (O S : Finset F) (h : O.card < S.card) :
    ∃ μ : F → F, I.IsMinInjection O S μ ∧ ∀ i ∈ S ∩ O, μ i = i := by sorry

end FacilityIncompatibilities.UniformMatroid

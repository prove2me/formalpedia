-- Prove2me | Theorems.Thm_FacilityIncompatibilities_UniformMatroid_lemma_13
-- name    : FacilityIncompatibilities.UniformMatroid.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:32.850252+00:00
-- url     : https://prove2.me/theorems/2160e499-7bc5-4961-b163-0c5cd1fc47c0
-- title:
--   Lemma 13 — exchange-sequence inequality for a minimum-cost injection
-- statement:
--   Let $d$ be the (pseudo)metric of an FL-MI instance, $O,S\subseteq V_F$, and let $\mu:O\to S$ be an injection minimizing $\sum_{o\in O}d(o,\mu(o))$. For every unmatched facility $t\in S\setminus\mu(O)$, every $\ell\ge 0$ and every sequence $o_0,o_1,\dots,o_\ell\in O$, with repetitions allowed,
--
--   $$d(o_0,t)+\sum_{r=1}^{\ell}d\big(o_r,\mu(o_{r-1})\big)\ \ge\ \sum_{r=0}^{\ell}d\big(o_r,\mu(o_r)\big).\tag{9}$$
--
--   This inequality compares the cost of the reassignment chain in the proof of Lemma 14 with its original cost.
--
--   Differences from the source:
--   - generalization: metric distances d on V_C ∪ V_F (Definition 1) → a pseudometric: d(x,x)=0, symmetry and the triangle inequality, distinct points may be at distance 0; reason: every metric satisfies these axioms, so every instance of the source is covered
--   - generalization: O, S the fixed solutions of §2.1 → any finite facility sets O, S; reason: the statement and proof use only the minimality of μ; the §2.1 sets are a special case
--   - encoding: an injection μ : O → S → a function μ : F → F with μ(O) ⊆ S and injective on O; values off O are irrelevant; reason: Lean convention; the same injections
--   - encoding: a sequence o_0, …, o_ℓ ∈ O → ℓ : ℕ and o : ℕ → F with o r ∈ O for r ≤ ℓ (values beyond ℓ unused); reason: Lean convention; the same sequences
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Lemma 13, eq. (9), printed p.10 / PDF p.11; proof printed pp.10–11 / PDF pp.11–12

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Compression

namespace FacilityIncompatibilities.UniformMatroid

/-- **Lemma 13** (printed p.10 / PDF p.11), inequality (9): let `μ : O → S` be an injection
minimizing `∑_{o ∈ O} d(o, μ(o))`. For every unmatched `t ∈ S \ μ(O)` and every sequence
`o_0, …, o_ℓ ∈ O` (repetitions allowed),
`d(o_0, t) + ∑_{r=1}^{ℓ} d(o_r, μ(o_{r−1})) ≥ ∑_{r=0}^{ℓ} d(o_r, μ(o_r))`. -/
theorem lemma_13 {C F : Type*} [DecidableEq F] (I : Instance C F) (hI : I.Valid)
    (O S : Finset F) (μ : F → F) (hμ : I.IsMinInjection O S μ)
    (t : F) (htS : t ∈ S) (htμ : t ∉ O.image μ) (ℓ : ℕ) (o : ℕ → F) (ho : ∀ r ≤ ℓ, o r ∈ O) :
    ∑ r ∈ Finset.range (ℓ + 1), I.fdist (o r) (μ (o r)) ≤
      I.fdist (o 0) t + ∑ r ∈ Finset.Icc 1 ℓ, I.fdist (o r) (μ (o (r - 1))) := by sorry

end FacilityIncompatibilities.UniformMatroid

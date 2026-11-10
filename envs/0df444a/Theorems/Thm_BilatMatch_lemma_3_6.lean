-- Prove2me | Theorems.Thm_BilatMatch_lemma_3_6
-- name    : BilatMatch.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:12:30.993205+00:00
-- url     : https://prove2.me/theorems/90b48b89-a8f6-4414-a37d-8dc3ee8d2f1e
-- title:
--   Lemma 3.6 (Fixed-Multiplier Optimization) — $M^\alpha$ maximizes $L_\alpha$, is pointwise monotone, and trades only when $v_i>c_j$
-- statement:
--   Consider a market with finitely many agents, finitely supported priors and a nonempty downward-closed family of matchings, and fix $\alpha\ge0$. The ironed matching rule $M^\alpha$ maximizes the Lagrangian: $1_{M^\alpha}\in X$ and $L_\alpha(1_{M^\alpha})\ge L_\alpha(x)$ for every $x\in X$. With all other reports fixed, each buyer's trade probability is nondecreasing in her value and each seller's is nonincreasing in her cost (pointwise monotonicity). Moreover $M^\alpha$ trades only when $v_i>c_j$.
--
--   **Formalization Note** Profiles and reports range over the supports; the tie-breaking order is an injective rank on $\mathcal F$.
--
--   Differences from the source:
--   - encoding: M^α maximizes the Lagrangian → 1_{M^α} ∈ X and L_α(1_{M^α}) ≥ L_α(x) for all x ∈ X; reason: the Lagrangian problem is max over X (Lemma 2.1)
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Lemma 3.6, p.14 (pdf p.16)

import Mathlib
import Definitions.Def_BilatMatch_iron

open MeasureTheory

namespace BilatMatch

/-- **Lemma 3.6 (Fixed-Multiplier Optimization).** Liu, Qin, Wang, arXiv:2609.30702 (held version,
sha256 ff1490ad…), Lemma 3.6, p.14 (pdf p.16).

For markets with finitely many agents and finitely supported priors and `α ≥ 0`, the ironed matching
rule `M^α` maximizes the Lagrangian `L_α` over `X`; with all other reports fixed, each buyer's trade
probability is nondecreasing in her value and each seller's is nonincreasing in her cost (pointwise
monotonicity); and `M^α` trades only when `v_i > c_j`.

**Formalization Note** `M^α(θ)` maximizes `∑_{(i,j) ∈ M} (ϕ̄^α_i(v_i) − τ̄^α_j(c_j))` over `F`, with the
fewest edges among maximizers and remaining ties broken by a fixed injective rank. Profiles and
reports range over the supports (p.6). "Maximizes the Lagrangian" is: `1_{M^α} ∈ X` and
`L_α(1_{M^α}) ≥ L_α(x)` for all `x ∈ X`. -/
theorem lemma_3_6 (α : ℝ) (hα : 0 ≤ α) {B S : Type*} [Fintype B] [Fintype S] (I : Market B S)
    (hI : I.IsValid) (hB : ∀ i, IsFiniteSupport (I.buyerLaw i))
    (hS : ∀ j, IsFiniteSupport (I.sellerLaw j)) (rank : Set (B × S) → ℕ)
    (hrank : IsTieOrder I rank) :
    (InX I (ironedAlloc I rank α) ∧
      ∀ x : Allocation B S, InX I x → lagrangian I α x ≤ lagrangian I α (ironedAlloc I rank α)) ∧
    (∀ θ ∈ supportProfiles I, ∀ i, ∀ v ∈ atoms (I.buyerLaw i), ∀ v' ∈ atoms (I.buyerLaw i),
      v ≤ v' → allocXB (ironedAlloc I rank α) i (updateBuyer θ i v) ≤
        allocXB (ironedAlloc I rank α) i (updateBuyer θ i v')) ∧
    (∀ θ ∈ supportProfiles I, ∀ j, ∀ c ∈ atoms (I.sellerLaw j), ∀ c' ∈ atoms (I.sellerLaw j),
      c ≤ c' → allocXS (ironedAlloc I rank α) j (updateSeller θ j c') ≤
        allocXS (ironedAlloc I rank α) j (updateSeller θ j c)) ∧
    (∀ θ ∈ supportProfiles I, ∀ e ∈ ironedMatching I rank α θ, θ.2 e.2 < θ.1 e.1) := by sorry

end BilatMatch

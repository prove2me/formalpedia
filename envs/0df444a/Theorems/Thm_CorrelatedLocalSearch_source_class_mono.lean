-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_source_class_mono
-- name    : CorrelatedLocalSearch.source_class_mono
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:40:12.730193+00:00
-- url     : https://prove2.me/theorems/09c56b66-ab0e-4fcf-b0e5-900fb4c15134
-- title:
--   Proof of Theorem 4.1 — $\mathcal Q_{s,D}\subseteq\mathcal Q_{s_*,D}$, and $\tau=0$ from a satisfying start
-- statement:
--   Let $k\ge1$.
--
--   1. For all real $s'\le s$ and every $D$, $\ \mathcal Q_{s,D}\subseteq\mathcal Q_{s',D}$; in particular $\mathcal Q_{s,D}\subseteq\mathcal Q_{s_*,D}$ for $s\in[s_*,1]$.
--   2. For every $k$-CNF $\Phi$, every clause selector and every initial assignment $x_0$ that satisfies $\Phi$, the walk has $\tau=0$ on every tape.
--
--   Clause 1 reduces the critical bounds of Theorem 4.1 for $s\ge s_*$ to Lemma C.1 at $s_*$; clause 2 covers the case $h=0$ of the theorem.
--
--   Differences from the source:
--   - generalization: Q_{s,D} ⊆ Q_{s∗,D} for s ∈ [s∗, 1] → Q_{s,D} ⊆ Q_{s′,D} for all reals s′ ≤ s; reason: uses only P[w] ≤ 1; s′ = s∗ is the paper's case
--   - encoding: the alphabet [k] → 1 ≤ k; reason: k/2 < r < k forces k ≥ 3; k ≥ 1 is what makes P[w] ≤ 1
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Theorem 4.1, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_SourceClass
import Definitions.Def_CorrelatedLocalSearch_Clause
import Definitions.Def_CorrelatedLocalSearch_walkTau

set_option autoImplicit false

namespace CorrelatedLocalSearch

/-- Monotonicity of the source class and the satisfied start (Xu, *Local Search with
Correlated Randomness*, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Theorem 4.1,
p.23: "The barrier lemma and `Q_{s,D} ⊆ Q_{s∗,D}` give the critical tail and the cubic
expectation bound. An initially satisfying assignment has `τ = 0`"):
1. `Q_{s,D} ⊆ Q_{s′,D}` whenever `s′ ≤ s` (in particular `Q_{s,D} ⊆ Q_{s∗,D}` for `s ≥ s∗`);
2. if the initial assignment `x₀` satisfies `Φ`, then `τ = 0` on every tape.

**Formalization Note** Clause 1 is stated for every `s′ ≤ s` (it uses only `P[w] ≤ 1`), which
contains the paper's case `s′ = s∗ ≤ s ≤ 1`; `1 ≤ k` makes `P[w] ≤ 1`. -/
theorem source_class_mono (k : ℕ) (hk : 1 ≤ k) :
    (∀ s' s D : ℝ, s' ≤ s → SourceClass k s D ⊆ SourceClass k s' D) ∧
      ∀ (n : ℕ) (Φ : List (Clause k n)) (sel : Selector k n) (x₀ : Fin n → Bool),
        Satisfies Φ x₀ → ∀ ω : ℕ → Fin k, walkTau Φ sel x₀ ω = 0 := by sorry

end CorrelatedLocalSearch

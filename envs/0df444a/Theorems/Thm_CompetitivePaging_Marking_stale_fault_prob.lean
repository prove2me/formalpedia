-- Prove2me | Theorems.Thm_CompetitivePaging_Marking_stale_fault_prob
-- name    : CompetitivePaging.Marking.stale_fault_prob
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:11:54.777408+00:00
-- url     : https://prove2.me/theorems/49ef3563-ec8e-40b9-9530-d4f0132117ca
-- title:
--   A stale request is a fault with probability $c/s$
-- statement:
--   Let $M$ be a set of $n$ vertices enumerated as $e(0), \dots, e(n-1)$, let $1 \le k \le n$, and run the marking algorithm with $k$ servers from $V = \{e(0), \dots, e(k-1)\}$ on a request sequence $\sigma$. Let request $i$ start a phase and let $t \ge i$ be an index such that no request with index in $(i, t]$ starts a phase, so that request $t$ belongs to the phase starting at $i$. Let $\mathrm{mk}_i$ be the marked set just before the phase (the vertices requested in the previous phase, or $V$ for the first phase) and $R(i,t)$ the set of vertices requested at indices $i, \dots, t-1$. Suppose $\sigma(t)$ is **stale**: $\sigma(t) \in \mathrm{mk}_i$ and $\sigma(t) \notin R(i,t)$. Put
--   $$c = |R(i,t) \setminus \mathrm{mk}_i|, \qquad s = |\mathrm{mk}_i \setminus R(i,t)|,$$
--   the number of clean vertices requested in the phase so far and the current number of stale vertices. Then the probability that $\sigma(t)$ is not covered just before it is served is
--   $$\Pr[\sigma(t) \notin \mathrm{cov}] = \frac{c}{s}.$$
--
--   This is the expected cost of a request to a stale vertex, the key probabilistic input to the bound on the marking algorithm's cost in a phase.
--
--   **Formalization Note.** The probability is taken under the law of the algorithm's state after the first $t$ requests and is stated in $[0,\infty]$; $s \ge 1$ because $\sigma(t)$ itself is stale.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 4, §3, proof of Theorem 1

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm

open scoped ENNReal

namespace CompetitivePaging.Marking

/-- §3, proof of Theorem 1 (p. 4): a request to a stale vertex (requested in the previous
phase, not yet in this phase) is a fault with probability `c/s`, where `c` is the number of
clean vertices requested in the phase so far and `s` the current number of stale vertices. -/
theorem stale_fault_prob {n k : ℕ} {M : Type*} [DecidableEq M]
    (e : Fin n ≃ M) (hk : 1 ≤ k) (hkn : k ≤ n) (σ : List M) (i t : ℕ) (ht : t < σ.length)
    (hi : IsPhaseStart k (initVertices e hkn) σ i) (hit : i ≤ t)
    (hno : ∀ u, i < u → u ≤ t → ¬ IsPhaseStart k (initVertices e hkn) σ u)
    (hstale : σ.get ⟨t, ht⟩ ∈ marksAt k (initVertices e hkn) σ i)
    (hnew : σ.get ⟨t, ht⟩ ∉ phaseRequested σ i t) :
    faultProb k (initVertices e hkn) (σ.take t) (σ.get ⟨t, ht⟩) =
      ((phaseRequested σ i t \ marksAt k (initVertices e hkn) σ i).card : ℝ≥0∞)
        / ((marksAt k (initVertices e hkn) σ i \ phaseRequested σ i t).card : ℝ≥0∞) := by sorry

end CompetitivePaging.Marking

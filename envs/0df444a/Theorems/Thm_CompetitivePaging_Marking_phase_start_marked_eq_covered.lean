-- Prove2me | Theorems.Thm_CompetitivePaging_Marking_phase_start_marked_eq_covered
-- name    : CompetitivePaging.Marking.phase_start_marked_eq_covered
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:09:24.663988+00:00
-- url     : https://prove2.me/theorems/edb4d06b-e514-4ea8-b720-fc236eddee2e
-- title:
--   At the start of every phase the marked vertices are the covered ones
-- statement:
--   Let $M$ be a set of $n$ vertices enumerated as $e(0), \dots, e(n-1)$, let $1 \le k \le n$, and run the marking algorithm with $k$ servers starting from the covered and marked set $V = \{e(0), \dots, e(k-1)\}$. Let $\sigma$ be a request sequence and let request $t$ start a phase, i.e. the marked set $\mathrm{mk}_t$ after the first $t$ requests satisfies $|\mathrm{mk}_t \cup \{\sigma(t)\}| = k+1$.
--
--   Then for every state $(\mathrm{cov}, \mathrm{mk})$ that the algorithm reaches with positive probability after the first $t$ requests,
--   $$\mathrm{mk} = \mathrm{cov} \quad\text{and}\quad \sigma(t) \notin \mathrm{mk}.$$
--
--   In words: at the start of every phase the marked vertices are precisely the ones occupied by the algorithm's servers, and the first request of every phase is to an unmarked vertex. This is the structural fact that makes the phase analysis of Theorem 1 possible: at every phase boundary the random configuration of the marking algorithm is in fact determined by the request sequence.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 4, §3, proof of Theorem 1

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm

namespace CompetitivePaging.Marking

/-- §3, proof of Theorem 1 (p. 4): at the start of every phase the marked vertices are
precisely the ones occupied by the marking algorithm's servers, and the first request of the
phase is to an unmarked vertex. -/
theorem phase_start_marked_eq_covered {n k : ℕ} {M : Type*} [DecidableEq M]
    (e : Fin n ≃ M) (hk : 1 ≤ k) (hkn : k ≤ n) (σ : List M) (t : ℕ) (ht : t < σ.length)
    (hstart : IsPhaseStart k (initVertices e hkn) σ t) :
    ∀ s ∈ (lawAfter k (initVertices e hkn) (σ.take t)).support,
      s.marked = s.covered ∧ σ.get ⟨t, ht⟩ ∉ s.marked := by sorry

end CompetitivePaging.Marking

-- Prove2me | Theorems.Thm_CompetitivePaging_Marking_phase_expected_cost_le
-- name    : CompetitivePaging.Marking.phase_expected_cost_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:12:23.510994+00:00
-- url     : https://prove2.me/theorems/71c0f0d1-1cfb-4aa1-bf96-c6527d58ed22
-- title:
--   The marking algorithm's expected cost in a phase is at most $l(H_k - H_l + 1) \le l H_k$
-- statement:
--   Let $M$ be a set of $n$ vertices enumerated as $e(0), \dots, e(n-1)$, let $1 \le k \le n$, and run the marking algorithm with $k$ servers from $V = \{e(0), \dots, e(k-1)\}$ on a request sequence $\sigma$. Let requests $i, \dots, i'-1$ form a complete phase, let $l = |R(i,i') \setminus \mathrm{mk}_i|$ be the number of requests to clean vertices in the phase, and let $C_M(i,i')$ be the expected cost of the marking algorithm on the requests of the phase (the sum of their fault probabilities). With $H_m = 1 + \frac12 + \dots + \frac1m$ the $m$-th harmonic number,
--   $$C_M(i,i') \le l\,(H_k - H_l + 1) \le l\,H_k.$$
--
--   Together with the adversary's amortized cost of at least $l/2$ per phase, this gives the competitive factor $2H_k$ of Theorem 1.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 5, §3, proof of Theorem 1 (displayed bound)

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm

namespace CompetitivePaging.Marking

/-- §3, proof of Theorem 1 (pp. 4–5): in a complete phase with `l` requests to clean vertices,
the expected cost of the marking algorithm is at most `l (H_k - H_l + 1) ≤ l H_k`. -/
theorem phase_expected_cost_le {n k : ℕ} {M : Type*} [DecidableEq M]
    (e : Fin n ≃ M) (hk : 1 ≤ k) (hkn : k ≤ n) (σ : List M) (i i' : ℕ)
    (hphase : IsCompletePhase k (initVertices e hkn) σ i i') :
    markingPhaseCost k (initVertices e hkn) σ i i'
        ≤ ((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          * ((harmonic k : ℝ)
            - (harmonic (phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
            + 1) ∧
      ((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          * ((harmonic k : ℝ)
            - (harmonic (phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
            + 1)
        ≤ ((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          * (harmonic k : ℝ) := by sorry

end CompetitivePaging.Marking

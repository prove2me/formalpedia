-- Prove2me | Theorems.Thm_CompetitivePaging_Marking_adversary_cost_ge_clean_sub_d
-- name    : CompetitivePaging.Marking.adversary_cost_ge_clean_sub_d
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:10:08.490431+00:00
-- url     : https://prove2.me/theorems/6c13d683-ae80-4b6d-ad2a-bf0e1607c4bc
-- title:
--   In a phase the adversary pays at least $l - d$
-- statement:
--   Let $M$ be a set of $n$ vertices with the uniform metric (distinct vertices at distance $1$), enumerated as $e(0), \dots, e(n-1)$, let $1 \le k \le n$, and consider the phases of the marking algorithm started from $V = \{e(0), \dots, e(k-1)\}$ on a request sequence $\sigma$. Let $S$ be a lazy schedule of $k$ servers on $\sigma$ (the adversary $A$; its starting configuration is arbitrary), and let requests $i, \dots, i'-1$ form a complete phase. Write $\mathrm{mk}_i$ for the marked set just before the phase (the vertices occupied by the marking algorithm's servers at the start of the phase) and $R(i,i')$ for the set of vertices requested in the phase. Put
--   1. $l = |R(i,i') \setminus \mathrm{mk}_i|$, the number of requests to clean vertices in the phase;
--   2. $d$ = the number of servers $j$ of $A$ with $S_i(j) \notin \mathrm{mk}_i$, i.e. the number of $A$'s servers that do not coincide with any of the marking algorithm's servers at the beginning of the phase;
--   3. $C_A = \sum_{t=i}^{i'-1} \mathrm{dist}(S_t, S_{t+1})$, the cost incurred by $A$ in the phase.
--
--   Then
--   $$C_A \ge l - d.$$
--
--   This is the first of the two lower bounds on the adversary's cost in a phase used in the proof of Theorem 1.
--
--   **Formalization Note.** The marking algorithm's servers at the start of a phase are identified with the (deterministic) marked set there; the preceding milestone shows that the two coincide with probability one. For the first phase the "previous phase" is the initial configuration $V$.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 4, §3, proof of Theorem 1

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm

namespace CompetitivePaging.Marking

/-- §3, proof of Theorem 1 (p. 4): in a complete phase, a lazy adversary `A` pays at least
`l - d`, where `l` is the number of clean vertices requested in the phase and `d` is the
number of `A`'s servers outside the marking algorithm's servers (= the marked set) at the
start of the phase. -/
theorem adversary_cost_ge_clean_sub_d {n k : ℕ} {M : Type*} [MetricSpace M] [DecidableEq M]
    (e : Fin n ≃ M) (hdist : ∀ x y : M, x ≠ y → dist x y = 1) (hk : 1 ≤ k) (hkn : k ≤ n)
    (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S) (i i' : ℕ)
    (hphase : IsCompletePhase k (initVertices e hkn) σ i i') :
    ((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
        - ((Finset.univ.filter
            (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ)
      ≤ ∑ t ∈ Finset.Ico i i', KServer.moveCost (S t) (S (t + 1)) := by sorry

end CompetitivePaging.Marking

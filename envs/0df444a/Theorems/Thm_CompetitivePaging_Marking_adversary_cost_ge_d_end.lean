-- Prove2me | Theorems.Thm_CompetitivePaging_Marking_adversary_cost_ge_d_end
-- name    : CompetitivePaging.Marking.adversary_cost_ge_d_end
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:10:50.404666+00:00
-- url     : https://prove2.me/theorems/232e58f3-6b30-4ca4-b8a4-6d7aa126491d
-- title:
--   In a phase a lazy adversary pays at least $d'$
-- statement:
--   Let $M$ be a set of $n$ vertices with the uniform metric, enumerated as $e(0), \dots, e(n-1)$, let $1 \le k \le n$, and consider the phases of the marking algorithm started from $V = \{e(0), \dots, e(k-1)\}$ on a request sequence $\sigma$. Let $S$ be a lazy schedule of $k$ servers on $\sigma$ (the adversary $A$), and let requests $i, \dots, i'-1$ form a complete phase. Let $\mathcal S = \mathrm{mk}_{i'}$ be the set of marked vertices at the end of the phase, let
--   $$d' = \#\{\,j : S_{i'}(j) \notin \mathcal S\,\}$$
--   be the number of $A$'s servers outside $\mathcal S$ at the end of the phase, and let $C_A = \sum_{t=i}^{i'-1} \mathrm{dist}(S_t, S_{t+1})$ be $A$'s cost in the phase. Then
--   $$C_A \ge d'.$$
--
--   This is the second lower bound on the adversary's cost in a phase used in the proof of Theorem 1; unlike the first, it uses that the adversary is lazy.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 4, §3, proof of Theorem 1

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm

namespace CompetitivePaging.Marking

/-- §3, proof of Theorem 1 (p. 4): in a complete phase, a lazy adversary `A` pays at least
`d'`, the number of `A`'s servers outside the set `S` of marked vertices at the end of the
phase. -/
theorem adversary_cost_ge_d_end {n k : ℕ} {M : Type*} [MetricSpace M] [DecidableEq M]
    (e : Fin n ≃ M) (hdist : ∀ x y : M, x ≠ y → dist x y = 1) (hk : 1 ≤ k) (hkn : k ≤ n)
    (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S) (i i' : ℕ)
    (hphase : IsCompletePhase k (initVertices e hkn) σ i i') :
    ((Finset.univ.filter
        (fun j : Fin k => S i' j ∉ marksAt k (initVertices e hkn) σ i')).card : ℝ)
      ≤ ∑ t ∈ Finset.Ico i i', KServer.moveCost (S t) (S (t + 1)) := by sorry

end CompetitivePaging.Marking

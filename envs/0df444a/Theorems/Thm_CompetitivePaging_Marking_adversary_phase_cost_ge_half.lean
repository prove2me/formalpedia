-- Prove2me | Theorems.Thm_CompetitivePaging_Marking_adversary_phase_cost_ge_half
-- name    : CompetitivePaging.Marking.adversary_phase_cost_ge_half
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:11:21.997539+00:00
-- url     : https://prove2.me/theorems/f5dd5205-6314-4bad-bfea-7429dd0c1d6f
-- title:
--   In a phase the adversary pays at least $\max(l-d, d') \ge \frac12(l-d+d')$
-- statement:
--   In the setting of the two preceding milestones (uniform metric on $n$ vertices, $1 \le k \le n$, a lazy adversary schedule $S$ and a complete phase $i, \dots, i'-1$ of the marking algorithm started from $V = \{e(0), \dots, e(k-1)\}$), let $l$ be the number of clean vertices requested in the phase, $d$ the number of $A$'s servers outside the marking algorithm's servers at the start of the phase, $d'$ the same quantity at the end of the phase, and $C_A$ the adversary's cost in the phase. Then
--   $$C_A \ge \max(l - d,\ d') \ge \tfrac12\,(l - d + d').$$
--
--   Summed over the phases, the $d$ and $d'$ terms telescope, so up to an additive constant the adversary's cost is at least half the total number of clean requests; this is the adversary side of the comparison in Theorem 1.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 4, §3, proof of Theorem 1 (displayed inequality)

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_CompetitivePaging_Marking_markingAlgorithm

namespace CompetitivePaging.Marking

/-- §3, proof of Theorem 1 (p. 4): in a complete phase, a lazy adversary's cost `C_A`
satisfies `C_A ≥ max(l - d, d') ≥ (l - d + d')/2`. -/
theorem adversary_phase_cost_ge_half {n k : ℕ} {M : Type*} [MetricSpace M] [DecidableEq M]
    (e : Fin n ≃ M) (hdist : ∀ x y : M, x ≠ y → dist x y = 1) (hk : 1 ≤ k) (hkn : k ≤ n)
    (σ : List M) (S : ℕ → KServer.Config k M) (hlazy : IsLazySchedule σ S) (i i' : ℕ)
    (hphase : IsCompletePhase k (initVertices e hkn) σ i i') :
    max (((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          - ((Finset.univ.filter
              (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ))
        ((Finset.univ.filter
          (fun j : Fin k => S i' j ∉ marksAt k (initVertices e hkn) σ i')).card : ℝ)
        ≤ ∑ t ∈ Finset.Ico i i', KServer.moveCost (S t) (S (t + 1)) ∧
      (((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          - ((Finset.univ.filter
              (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ)
          + ((Finset.univ.filter
              (fun j : Fin k => S i' j ∉ marksAt k (initVertices e hkn) σ i')).card : ℝ)) / 2
        ≤ max (((phaseRequested σ i i' \ marksAt k (initVertices e hkn) σ i).card : ℝ)
          - ((Finset.univ.filter
              (fun j : Fin k => S i j ∉ marksAt k (initVertices e hkn) σ i)).card : ℝ))
        ((Finset.univ.filter
          (fun j : Fin k => S i' j ∉ marksAt k (initVertices e hkn) σ i')).card : ℝ) := by sorry

end CompetitivePaging.Marking

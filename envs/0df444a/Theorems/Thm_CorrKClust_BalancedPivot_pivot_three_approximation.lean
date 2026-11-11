-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_pivot_three_approximation
-- name    : CorrKClust.BalancedPivot.pivot_three_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:57.303262+00:00
-- url     : https://prove2.me/theorems/4bb1b58a-30bd-47f0-b533-bb41c2ef79b7
-- title:
--   [ACN05] (cited p. 2) — PIVOT is an expected 3-approximation
-- statement:
--   For any finite simple graph $G$, run PIVOT on a uniformly random arrival order $\sigma$, assigning each nonpivot to its earliest pivot neighbour. If $\Pi_\sigma$ is the resulting unrestricted clustering, then
--   $$\mathbb E_\sigma[\operatorname{Cost}_G(\Pi_\sigma)]\le3\operatorname{OPT}_{CC}(G).$$
--   This external result is an open milestone here, rather than an axiom or a hypothesis of the mission goal. It controls disagreements within and between pivot clusters.
--
--   Differences from the source:
--   - encoding: finite vertex set and unordered disagreements → Fintype V, SimpleGraph V, maps to labels, and unordered distinct Sym2 pairs; reason: decidable equality is classical data and no finite graph or clustering is excluded
--   - encoding: uniform random arrival order → the finite average over all bijections Fin (card V) ≃ V; reason: there are exactly n! such bijections, each with equal weight
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), [ACN05], cited p. 2 and used pp. 30, 37, p. 2, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- [ACN05], cited p. 2: online PIVOT on a uniform permutation is an expected 3-approximation. -/
theorem pivot_three_approximation {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    average (fun σ : ArrivalOrder V => (cost G (pivotAssignment G σ) : ℝ)) ≤
      3 * (optCC G : ℝ) := by sorry

end CorrKClust.BalancedPivot

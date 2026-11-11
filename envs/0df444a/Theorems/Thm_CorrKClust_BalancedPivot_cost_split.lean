-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_cost_split
-- name    : CorrKClust.BalancedPivot.cost_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:58.385971+00:00
-- url     : https://prove2.me/theorems/60eefb69-e394-4e0b-beb2-2d4283ba627c
-- title:
--   §7.3.4, cost split — base disagreements and merging cost
-- statement:
--   For a finite graph, $k\ge1$ and an admissible tie rule, let B_σ be the Balanced Pivot output and Π_σ the PIVOT clustering on the same order. Let $D_\sigma$ count types (i) and (ii): non-edges within pivot clusters and edges separated by the output. Let $M_\sigma$ count non-edges between distinct pivot clusters merged in the output. For every order,
--   $$\operatorname{Cost}_G(B_\sigma)=D_\sigma+M_\sigma,\qquad D_\sigma\le\operatorname{Cost}_G(\Pi_\sigma).$$
--   Moreover,
--   $$\mathbb E[D_\sigma]\le3\operatorname{OPT}_k(G),\qquad\mathbb E[\operatorname{Cost}_G(B_\sigma)]\le3\operatorname{OPT}_k(G)+\mathbb E[M_\sigma].$$
--   This includes the deterministic split and the passage's expectation claim; the remaining merging term is the subject of the two case milestones.
--
--   Differences from the source:
--   - encoding: finite vertex set and unordered disagreements → Fintype V, SimpleGraph V, maps to labels, and unordered distinct Sym2 pairs; reason: decidable equality is classical data and no finite graph or clustering is excluded
--   - encoding: at most k possibly empty clusters → k > 0 and assignments V → Fin k; reason: positive k is required for an assignment on nonempty inputs and all unused labels remain legal
--   - encoding: uniform random arrival order → the finite average over all bijections Fin (card V) ≃ V; reason: there are exactly n! such bijections, each with equal weight
--   - reading: assign to the cluster with minimal size, with ties unspecified → every history-dependent rule returning a minimum-current-size cluster; reason: the proof uses only minimality and the absolute constant must be uniform over these choices
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), §7.3.4, cost split, p. 37, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- §7.3.4, p. 37: deterministic split and both expectation consequences. -/
theorem cost_split {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {k : ℕ} (hk : 0 < k) (ρ : TieRule V k) (hρ : Admissible ρ) :
    (∀ σ : ArrivalOrder V,
      cost G (balancedAssignment hk G ρ σ) = baseCost hk G ρ σ + mergeCost hk G ρ σ ∧
      baseCost hk G ρ σ ≤ cost G (pivotAssignment G σ)) ∧
    average (fun σ : ArrivalOrder V => (baseCost hk G ρ σ : ℝ)) ≤ 3 * (optK G k : ℝ) ∧
    average (fun σ : ArrivalOrder V => (cost G (balancedAssignment hk G ρ σ) : ℝ)) ≤
      3 * (optK G k : ℝ) + average (fun σ : ArrivalOrder V => (mergeCost hk G ρ σ : ℝ)) := by sorry

end CorrKClust.BalancedPivot

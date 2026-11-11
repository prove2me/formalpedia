-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_balanced_pivot_competitive
-- name    : CorrKClust.BalancedPivot.balanced_pivot_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:13.087099+00:00
-- url     : https://prove2.me/theorems/54ff6790-4294-49bd-904e-0ba3c1a3fc75
-- title:
--   Theorem 4 — Balanced Pivot is O(log⁴ n)-competitive in expectation
-- statement:
--   There exists an absolute constant C > 0 such that for every finite simple graph G = (V,E), with n = |V|, every integer k ≥ 1 and every admissible history-dependent rule ρ for breaking minimum-current-size ties in Algorithm 1,
--   $$\frac1{n!}\sum_{\sigma}\operatorname{Cost}_G(\operatorname{BalancedPivot}_{\rho}(G,k,\sigma))\le C(\ln n)^4\operatorname{OPT}_k(G).$$
--   The sum ranges over all n! arrival orders with equal weight. OPT_k ranges over every assignment to at most k clusters, with empty labels allowed. There is no additive term, restriction on graph structure, or upper bound on k. Empty and singleton inputs have zero disagreement cost. The constant precedes the vertex type, graph, k and rule.
--
--   This is the paper's main random-order upper bound for general graphs. Algorithm 1 is defined by its actual sequential updates, independently of the desired inequality. External concentration estimates and the PIVOT approximation result are milestones, not assumptions of this theorem.
--
--   Differences from the source:
--   - encoding: finite vertex set and unordered disagreements → Fintype V, SimpleGraph V, maps to labels, and unordered distinct Sym2 pairs; reason: decidable equality is classical data and no finite graph or clustering is excluded
--   - encoding: every finite vertex set → vertex types V : Type (universe 0); reason: every finite vertex set is in bijection with Fin n : Type, and cost, OPT_k and the algorithm transfer along such bijections
--   - encoding: at most k possibly empty clusters → k > 0 and assignments V → Fin k; reason: positive k is required for an assignment on nonempty inputs and all unused labels remain legal
--   - encoding: uniform random arrival order → the finite average over all bijections Fin (card V) ≃ V; reason: there are exactly n! such bijections, each with equal weight
--   - encoding: logarithmic competitive ratio → Real.log n, the natural logarithm; reason: changing the fixed logarithm base changes only the existential absolute constant
--   - reading: assign to the cluster with minimal size, with ties unspecified → every history-dependent rule returning a minimum-current-size cluster; reason: the proof uses only minimality and the absolute constant must be uniform over these choices
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Theorem 4; also pp. 4, 37, p. 29, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Definitions.Def_CorrKClust_BalancedPivot_Analysis

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- Theorem 4, p. 29. Every finite graph, every k ≥ 1, every admissible tie rule;
all n! orders have equal weight, and the absolute constant precedes every instance. -/
theorem balanced_pivot_competitive : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      (k : ℕ) (hk : 0 < k) (ρ : TieRule V k), Admissible ρ →
      average (fun σ : ArrivalOrder V => (cost G (balancedAssignment hk G ρ σ) : ℝ)) ≤
        C * Real.log (Fintype.card V) ^ 4 * (optK G k : ℝ) := by sorry

end CorrKClust.BalancedPivot

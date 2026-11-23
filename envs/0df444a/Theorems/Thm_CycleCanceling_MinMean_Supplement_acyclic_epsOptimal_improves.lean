-- Prove2me | Theorems.Thm_CycleCanceling_MinMean_Supplement_acyclic_epsOptimal_improves
-- name    : CycleCanceling.MinMean.Supplement.acyclic_epsOptimal_improves
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:22:56.327787+00:00
-- url     : https://prove2.me/theorems/ee736c46-5934-4b0a-9f50-2a48d63429e5
-- title:
--   Lemma 3.4 — acyclicity improves existential ε-optimality
-- statement:
--   Let $N$ be a finite symmetric network with $n=|V|$ vertices, $f$ a circulation, $p$ any vertex-price function, and $\varepsilon\ge0$. Suppose every residual arc satisfies $c_p(v,w)\ge-\varepsilon$ and the graph of residual arcs with strictly negative reduced cost is acyclic. Then
--
--   $$f\text{ is }(1-1/n)\varepsilon\text{-optimal}.$$
--
--   The conclusion includes existence of suitable prices for the smaller error. It does not require the original $p$ to witness the improved error. This supports the availability of the price-tightening step in Theorem 4.1, for arbitrary real costs.
--
--   **Formalization Note** Circulation, nonnegative error, fixed-price constraints and acyclicity are explicit premises. There is no cost-integrality premise, no restriction on $n$ or $m$ (the source's $m\ge n\ge2$ convention is for time bounds only) and no assumed attainment of $\varepsilon(f)$.
--
--   Differences from the source:
--   - encoding: circulations and cycles on a finite symmetric graph → published CircNetwork, IsCirculation, IsMinCost and residual simple-cycle conventions; reason: the same symmetric directed arcs, arbitrary real capacities and real flows are retained; m counts both orientations
--   - encoding: acyclic G(f,p) and improved ε-optimality → no admissible residual simple cycle; IsEpsOptimal at the improved error; reason: a finite directed graph has a cycle exactly when it has a simple cycle, and IsEpsOptimal existentially quantifies the new prices
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, https://doi.org/10.1145/76359.76368, p. 878, Lemma 3.4

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Supplement_Admissible

namespace CycleCanceling.MinMean.Supplement

/-- Lemma 3.4, p. 878: the improved error is witnessed by some prices,
which need not be the original prices p. No restriction on n is imposed. -/
theorem acyclic_epsOptimal_improves
    {V : Type*} [Fintype V] [DecidableEq V] (N : CircNetwork V)
    (f : V → V → ℝ) (p : V → ℝ) (ε : ℝ)
    (hf : IsCirculation N f) (hε : 0 ≤ ε)
    (hp : IsEpsOptimalWrt N f ε p) (hacyclic : IsAdmissibleAcyclic N f p) :
    IsEpsOptimal N f ((1 - 1 / (Fintype.card V : ℝ)) * ε) := by sorry

end CycleCanceling.MinMean.Supplement

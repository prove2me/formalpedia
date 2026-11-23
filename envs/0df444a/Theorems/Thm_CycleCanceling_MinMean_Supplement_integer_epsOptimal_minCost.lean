-- Prove2me | Theorems.Thm_CycleCanceling_MinMean_Supplement_integer_epsOptimal_minCost
-- name    : CycleCanceling.MinMean.Supplement.integer_epsOptimal_minCost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:21:06.299576+00:00
-- url     : https://prove2.me/theorems/c043d649-e736-4d40-b111-f4cfae2666ba
-- title:
--   Theorem 3.2 — integer-cost ε-optimality threshold
-- statement:
--   Let $N$ be a finite symmetric circulation network with $n=|V|$ vertices. Assume every arc cost is an integer; capacities may be arbitrary real numbers. For any $\varepsilon$-optimal circulation $f$, if $0\le\varepsilon<1/n$, then
--
--   $$\operatorname{cost}(f)\le\operatorname{cost}(g)\quad\text{for every circulation }g.$$
--
--   Thus approximate optimality below this strict threshold certifies exact minimum cost, including against nonintegral competing circulations. Nonnegativity of $\varepsilon$, feasibility and existence of witnessing prices are contained in the published $\varepsilon$-optimality predicate.
--
--   **Formalization Note** No restriction on $n$ or $m$ is imposed: the source's convention $m\ge n\ge2$ (p. 874) is stated for time bounds only, and the theorem holds as printed for every $n$. The proof on p. 877 prints $n\varepsilon>-1$; the correct lower estimate is $-n\varepsilon>-1$, without changing the theorem statement.
--
--   Differences from the source:
--   - encoding: circulations and cycles on a finite symmetric graph → published CircNetwork, IsCirculation, IsMinCost and residual simple-cycle conventions; reason: the same symmetric directed arcs, arbitrary real capacities and real flows are retained; m counts both orientations
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, https://doi.org/10.1145/76359.76368, p. 877, Theorem 3.2

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal

namespace CycleCanceling.MinMean.Supplement

/-- Theorem 3.2 [5], p. 877: the strict integer-cost optimality threshold.
Capacities and both the given and competing circulations are real-valued.
No restriction on n: the source's m ≥ n ≥ 2 convention is for time bounds only. -/
theorem integer_epsOptimal_minCost
    {V : Type*} [Fintype V] [DecidableEq V] (N : CircNetwork V)
    (hInt : ∀ v w, (v, w) ∈ N.E → ∃ z : ℤ, N.c v w = (z : ℝ))
    (f : V → V → ℝ) (ε : ℝ)
    (hε : IsEpsOptimal N f ε) (hsmall : ε < 1 / (Fintype.card V : ℝ)) :
    IsMinCost N f := by sorry

end CycleCanceling.MinMean.Supplement

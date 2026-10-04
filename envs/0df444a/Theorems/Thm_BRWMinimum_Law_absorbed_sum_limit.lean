-- Prove2me | Theorems.Thm_BRWMinimum_Law_absorbed_sum_limit
-- name    : BRWMinimum.Law.absorbed_sum_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:43:22.073149+00:00
-- url     : https://prove2.me/theorems/d369d61d-ca6d-43a7-84f9-2e376127e88a
-- title:
--   §5, eq. (5.2) — lim_{A→∞} Σ_{u∈𝒵[A]} V(u)e^{−V(u)} = D_∞ almost surely
-- statement:
--   Under the standing assumptions (1.1), non-lattice $\mathcal L$, (1.3), (1.4), let $\mathcal Z[A]=\{u\in\mathbb T: V(u)\ge A,\ V(u_k)<A\ \forall k<|u|\}$ be the set of particles absorbed at level $A$ (the first particles of each line of descent to reach $[A,\infty)$), for the branching random walk started at $0$. Then, almost surely,
--   $$\lim_{A\to\infty}\sum_{u\in\mathcal Z[A]}V(u)e^{-V(u)}=D_\infty,$$
--   the limit of the derivative martingale.
--
--   In the proof of Theorem 1.1 this identifies the limit law: the minimum at time $n$ is the minimum over $u\in\mathcal Z[A]$ of independent copies started at $V(u)$, and the sum above is what remains after Proposition 4.1 is applied to each copy.
--
--   **Formalization Note** $\mathcal Z[A]$ is a random subset of the countable set of labels; the sum is a real `tsum`, absolutely summable almost surely, so its junk value $0$ on a null set is harmless. The limit is over real $A\to\infty$.
-- source:
--   Aïdékon, Convergence in law of the minimum of a branching random walk, arXiv:1101.1810v6 (Ann. Probab. 41 (2013)), p. 47 (definition of 𝒵[A]); p. 48, §5, eq. (5.2)

import Mathlib
import Definitions.Def_BRWMinimum_Law_PointProcess
import Definitions.Def_BRWMinimum_Law_BRW
import Definitions.Def_BRWMinimum_Law_RandomWalk

open MeasureTheory ProbabilityTheory Filter Topology

namespace BRWMinimum.Law

/-- §5, eq. (5.2): `lim_{A→∞} Σ_{u∈𝒵[A]} V(u) e^{−V(u)} = D_∞` almost surely. -/
theorem absorbed_sum_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : List ℕ → Ω → PointConfig} {L : Measure PointConfig} [IsProbabilityMeasure L]
    (hξ : IsBRW P ξ L)
    (h11 : BoundaryCase L) (hNL : NonLattice L) (h13 : SecondMoment L) (h14 : LogMoments L) :
    ∀ᵐ ω ∂P, Tendsto (fun A : ℝ => ∑' u : ↥(absorbed ξ A ω),
        pos ξ 0 u.1 ω * Real.exp (-pos ξ 0 u.1 ω)) atTop (𝓝 (derivMartLim ξ ω)) := by sorry

end BRWMinimum.Law

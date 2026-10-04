-- Prove2me | Theorems.Thm_BRWMinimum_Law_minimum_convergence_in_law
-- name    : BRWMinimum.Law.minimum_convergence_in_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:43:32.151983+00:00
-- url     : https://prove2.me/theorems/8bcb3823-1dbe-4a62-9fae-474b51bedbd0
-- title:
--   Theorem 1.1 — 𝐏(Mₙ ≥ (3/2) ln n + x) → 𝐄[exp(−C* eˣ D_∞)] for one C* ∈ (0, ∞) and every real x
-- statement:
--   Let $(V(x),x\in\mathbb T)$ be a branching random walk started at $0$ whose offspring point process $\mathcal L$ satisfies the boundary case (1.1), is non-lattice, and satisfies the moment conditions (1.3) and (1.4). Let $M_n=\min\{V(x):|x|=n\}$ (with $\min\varnothing=+\infty$) and let $D_\infty$ be the almost-sure limit of the derivative martingale $D_n=\sum_{|x|=n}V(x)e^{-V(x)}$. There exists a constant $C^*\in(0,\infty)$ such that for every real $x$,
--   $$\lim_{n\to\infty}\mathbf P\Big(M_n\ge\frac32\ln n+x\Big)=\mathbf E\Big[e^{-C^*e^{x}D_\infty}\Big].$$
--
--   Thus $M_n-\frac32\ln n$ converges in law to a Gumbel random variable shifted by $-\ln(C^*D_\infty)$ (on non-extinction); this is the branching-random-walk analogue of Bramson's and Lalley–Sellke's results for branching Brownian motion.
--
--   **Formalization Note** $M_n$ is an extended real, $+\infty$ when generation $n$ is empty, so the extinction event lies in $\{M_n\ge\frac32\ln n+x\}$, as in the paper. The constant $C^*$ is chosen before $x$. The expectation is a lower Lebesgue integral of $e^{-C^*e^xD_\infty}\in(0,1]$ ($D_\infty\ge0$ a.s.). $D_\infty$ is the pointwise limit of $D_n$, which exists almost surely (a milestone). $\ln n$ at $n=0$ is irrelevant for the limit.
-- source:
--   Aïdékon, Convergence in law of the minimum of a branching random walk, arXiv:1101.1810v6 (Ann. Probab. 41 (2013)), p. 3, Theorem 1.1, eq. (1.6)

import Mathlib
import Definitions.Def_BRWMinimum_Law_PointProcess
import Definitions.Def_BRWMinimum_Law_BRW
import Definitions.Def_BRWMinimum_Law_RandomWalk

open MeasureTheory ProbabilityTheory Filter Topology

namespace BRWMinimum.Law

/-- Theorem 1.1: there is `C* ∈ (0, ∞)` with
`P(M_n ≥ (3/2) ln n + x) → E[exp(−C* eˣ D_∞)]` for every real `x`. -/
theorem minimum_convergence_in_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : List ℕ → Ω → PointConfig} {L : Measure PointConfig} [IsProbabilityMeasure L]
    (hξ : IsBRW P ξ L)
    (h11 : BoundaryCase L) (hNL : NonLattice L) (h13 : SecondMoment L) (h14 : LogMoments L) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      Tendsto (fun n : ℕ => P {ω | (((3 / 2 : ℝ) * Real.log n + x : ℝ) : EReal) ≤ minPos ξ 0 n ω})
        atTop (𝓝 (∫⁻ ω, ENNReal.ofReal (Real.exp (-(C * Real.exp x * derivMartLim ξ ω))) ∂P)) := by sorry

end BRWMinimum.Law

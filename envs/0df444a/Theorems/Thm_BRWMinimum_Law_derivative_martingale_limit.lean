-- Prove2me | Theorems.Thm_BRWMinimum_Law_derivative_martingale_limit
-- name    : BRWMinimum.Law.derivative_martingale_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:43:18.5841+00:00
-- url     : https://prove2.me/theorems/45bbcada-64fb-4adb-97cd-1f42dad8e0f2
-- title:
--   §1, p. 3 — Dₙ → D_∞ a.s., D_∞ ≥ 0, D_∞ > 0 a.s. on non-extinction, and 𝕋 survives with positive probability
-- statement:
--   Let $(V(x),x\in\mathbb T)$ be a branching random walk started at $0$ satisfying (1.1), (1.3) and (1.4), and let $D_n=\sum_{|x|=n}V(x)e^{-V(x)}$ be the derivative martingale (1.5). Then:
--
--   1. almost surely, $D_n$ converges to a finite limit $D_\infty$;
--   2. almost surely, $D_\infty\ge0$;
--   3. almost surely on the event of non-extinction of $\mathbb T$, $D_\infty>0$;
--   4. $\mathbb T$ survives with positive probability.
--
--   The paper states this in §1 as "From [7] (and Proposition A.3 in the Appendix), we know that the martingale converges almost surely to some limit $D_\infty$, which is strictly positive on the set of non-extinction of $\mathbb T$. Notice that under (1.1), the tree $\mathbb T$ has a positive probability to survive." Proposition A.3 (iii) reads: "We have $D_\infty>0$ almost surely on the event of non-extinction of $\mathbb T$." $D_\infty$ is the random variable in the limit law of Theorem 1.1.
--
--   **Formalization Note** Item 2 is not printed on the page; it follows from the page's claims (on extinction $D_n$ is eventually the empty sum $0$) and is needed for the limit in Theorem 1.1 to lie in $[0,1]$. Non-extinction means every generation is nonempty. The non-lattice assumption is not used, as in Appendix A.
-- source:
--   Aïdékon, Convergence in law of the minimum of a branching random walk, arXiv:1101.1810v6 (Ann. Probab. 41 (2013)), p. 3, §1, sentence before Theorem 1.1; p. 53, Proposition A.3 (iii)

import Mathlib
import Definitions.Def_BRWMinimum_Law_PointProcess
import Definitions.Def_BRWMinimum_Law_BRW
import Definitions.Def_BRWMinimum_Law_RandomWalk

open MeasureTheory ProbabilityTheory Filter Topology

namespace BRWMinimum.Law

/-- §1, p. 3 (with Proposition A.3 (iii)): `D_n → D_∞` a.s., `D_∞ ≥ 0` a.s., `D_∞ > 0` a.s. on
non-extinction, and `𝕋` survives with positive probability. Hypotheses (1.1), (1.3), (1.4). -/
theorem derivative_martingale_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : List ℕ → Ω → PointConfig} {L : Measure PointConfig} [IsProbabilityMeasure L]
    (hξ : IsBRW P ξ L)
    (h11 : BoundaryCase L) (h13 : SecondMoment L) (h14 : LogMoments L) :
    (∀ᵐ ω ∂P, ∃ d : ℝ, Tendsto (fun n : ℕ => derivMart ξ n ω) atTop (𝓝 d)) ∧
      (∀ᵐ ω ∂P, 0 ≤ derivMartLim ξ ω) ∧
      (∀ᵐ ω ∂P, Survives ξ ω → 0 < derivMartLim ξ ω) ∧
      0 < P {ω | Survives ξ ω} := by sorry

end BRWMinimum.Law

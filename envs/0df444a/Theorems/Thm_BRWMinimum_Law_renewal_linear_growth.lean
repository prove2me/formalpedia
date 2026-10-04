-- Prove2me | Theorems.Thm_BRWMinimum_Law_renewal_linear_growth
-- name    : BRWMinimum.Law.renewal_linear_growth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:42:59.126305+00:00
-- url     : https://prove2.me/theorems/1e4695b1-6efa-4a1c-a1f9-57c436c9e88b
-- title:
--   §2.2, eq. (2.13) — the ladder-height renewal function satisfies R(x)/x → c₀ > 0
-- statement:
--   Let $S$ be the centred random walk of the many-to-one lemma, under the standing assumptions (1.1), non-lattice $\mathcal L$, (1.3), (1.4), and let $R$ be the renewal function (2.11) of its strict descending ladder heights. Then $R(x)<\infty$ for every $x$, and there exists $c_0>0$ such that
--   $$\lim_{x\to\infty}\frac{R(x)}{x}=c_0.$$
--
--   The constant $c_0$ is the second factor of the final constant $C^*=C_1c_0$ in Theorem 1.1.
--
--   **Formalization Note** $R$ is defined with values in $[0,\infty]$; finiteness is asserted, and the limit is of the real numbers $R(x)/x$. The paper deduces (2.13) from $\mathbf E|H_1|<\infty$ (which uses $\mathbf E[S_1^2]<\infty$, i.e. (1.3)) and the renewal theorem.
-- source:
--   Aïdékon, Convergence in law of the minimum of a branching random walk, arXiv:1101.1810v6 (Ann. Probab. 41 (2013)), p. 7, §2.2, eqs. (2.11)–(2.13)

import Mathlib
import Definitions.Def_BRWMinimum_Law_PointProcess
import Definitions.Def_BRWMinimum_Law_BRW
import Definitions.Def_BRWMinimum_Law_RandomWalk

open MeasureTheory ProbabilityTheory Filter Topology

namespace BRWMinimum.Law

/-- §2.2, eq. (2.13): the renewal function is finite and `R(x)/x → c₀ > 0`. -/
theorem renewal_linear_growth {L : Measure PointConfig} [IsProbabilityMeasure L]
    (h11 : BoundaryCase L) (hNL : NonLattice L) (h13 : SecondMoment L) (h14 : LogMoments L) :
    (∀ x : ℝ, renewalFn L x ≠ ⊤) ∧
      ∃ c₀ : ℝ, 0 < c₀ ∧ Tendsto (fun x : ℝ => (renewalFn L x).toReal / x) atTop (𝓝 c₀) := by sorry

end BRWMinimum.Law

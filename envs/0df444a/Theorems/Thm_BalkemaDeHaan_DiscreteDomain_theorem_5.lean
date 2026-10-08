-- Prove2me | Theorems.Thm_BalkemaDeHaan_DiscreteDomain_theorem_5
-- name    : BalkemaDeHaan.DiscreteDomain.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:36.448428+00:00
-- url     : https://prove2.me/theorems/667a8b2b-722f-457e-8cf6-e3f5913c3935
-- title:
--   Theorem 5 — F ∈ D_r(Π_{p,c}) iff F is tail equivalent to a discrete law satisfying (12a) and (12b)
-- statement:
--   Let $p > 0$ and $c \ge 0$, and let $F$ be a distribution function on $\mathbb R$. Then $F$ lies in the domain of residual life time attraction of the discrete limit law $\Pi_{p,c}$,
--   $$F_t\big(b(t) + x\,a(t)\big) \to \Pi_{p,c}(x) \quad \text{weakly as } t \to \infty \text{ for some } a(t) > 0,\ b(t),$$
--   if and only if $F$ is tail equivalent to a discrete distribution function $F_0 = 1 - R_0$ whose discontinuity points form an unbounded increasing sequence $t_0 < t_1 < \cdots$ with
--   $$\frac{t_{n+1}-t_n}{t_n - t_{n-1}} \to e^{pc} \ \ \text{(12a)}, \qquad \frac{R_0(t_{n+1})}{R_0(t_n)} \to e^{-p} \ \ \text{(12b)}.$$
--
--   Theorem 5 identifies the domains of attraction of all discrete residual-life limit laws: up to tail equivalence, they are exactly the laws whose atoms spread out at a geometric rate $e^{pc}$ while the tail drops by the factor $e^{-p}$ from atom to atom.
--
--   **Formalization Note** "Weakly" is convergence at the continuity points of $\Pi_{p,c}$ only; $\Pi_{p,c}$ is a step function and convergence at its jumps generally fails. Tail equivalence includes $F(x) < 1$ and $F_0(x) < 1$ for all $x$; for $F$ this also follows from $F \in D_r$.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 800 (PDF 9), Theorem 5

import Mathlib
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_ResidualLife
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_PiPC
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_DiscreteLaw

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.DiscreteDomain

/-- Theorem 5, p. 800 (PDF 9): for `p > 0` and `c ≥ 0`, `F ∈ D_r(Π_{p,c})` iff `F` is BalkemaDeHaan.LimitTypes.tail
equivalent to a discrete distribution function `F₀` whose jumps `t₀ < t₁ < ⋯ → ∞` satisfy
(12a) and (12b). -/
theorem theorem_5 (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    InDr μ (piPC p c) ↔
      ∃ ν₀ : Measure ℝ, IsProbabilityMeasure ν₀ ∧ ∃ t : ℕ → ℝ,
        IsDiscreteWithJumps ν₀ t ∧ GapRatio t p c ∧ TailRatio ν₀ t p ∧ TailEquiv μ ν₀ := by sorry

end BalkemaDeHaan.DiscreteDomain

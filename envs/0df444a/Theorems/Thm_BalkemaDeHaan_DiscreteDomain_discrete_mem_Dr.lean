-- Prove2me | Theorems.Thm_BalkemaDeHaan_DiscreteDomain_discrete_mem_Dr
-- name    : BalkemaDeHaan.DiscreteDomain.discrete_mem_Dr
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:14.870567+00:00
-- url     : https://prove2.me/theorems/31806240-44a6-4912-a9ef-15994733722f
-- title:
--   §3, p. 800 — a discrete law satisfying (12a) and (12b) lies in D_r(Π_{p,c})
-- statement:
--   Let $p > 0$ and $c \ge 0$. Let $F = 1 - R$ be a discrete distribution function, continuous from the right, whose discontinuity points form an unbounded increasing sequence $t_0 < t_1 < t_2 < \cdots$ such that
--   $$\frac{t_{n+1}-t_n}{t_n - t_{n-1}} \to e^{pc} \ \ \text{(12a)}, \qquad \frac{R(t_{n+1})}{R(t_n)} \to e^{-p} \ \ \text{(12b)}.$$
--   Then $F \in D_r(\Pi_{p,c})$: there are $a(t) > 0$ and $b(t)$ with $F_t(b(t) + x a(t)) \to \Pi_{p,c}(x)$ at every continuity point of $\Pi_{p,c}$.
--
--   This is the "if" half of Theorem 5 in its basic form: discrete laws whose atoms spread out geometrically and whose tail decays geometrically along the atoms are attracted to $\Pi_{p,c}$.
--
--   **Formalization Note** The page shows that the normed tails converge to a function of the *type* of $1 - \Pi_{p,c}$ (jumps at $0, e^{pc}, e^{pc} + e^{2pc}, \dots$, an affine image of the jumps of $\Pi_{p,c}$); since $D_r$ lets $a(t), b(t)$ be chosen freely, the statement is made with $\Pi_{p,c}$ itself. The page normalizes along $t = t_n$; the Lean asks for normalizations at every real $t \to \infty$, which is what $D_r$ means.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 800 (PDF 9), §3, the display after (12a)–(12b)

import Mathlib
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_ResidualLife
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_PiPC
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_DiscreteLaw

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.DiscreteDomain

/-- §3, p. 800 (PDF 9): a discrete law whose jumps `t₀ < t₁ < ⋯ → ∞` satisfy (12a) and (12b)
lies in the domain of residual life time attraction of `Π_{p,c}`. -/
theorem discrete_mem_Dr (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℕ → ℝ)
    (hν : IsDiscreteWithJumps ν t) (h12a : GapRatio t p c) (h12b : TailRatio ν t p) :
    InDr ν (piPC p c) := by sorry

end BalkemaDeHaan.DiscreteDomain

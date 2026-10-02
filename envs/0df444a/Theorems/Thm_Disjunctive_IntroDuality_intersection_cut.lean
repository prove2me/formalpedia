-- Prove2me | Theorems.Thm_Disjunctive_IntroDuality_intersection_cut
-- name    : Disjunctive.IntroDuality.intersection_cut
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:02:41.631879+00:00
-- url     : https://prove2.me/theorems/52404a4c-adf3-4fcd-8d76-0f6ae606bf8b
-- title:
--   Theorem 1.1 — the intersection cut
-- statement:
--   This is Theorem 1.1 of Balas's *Disjunctive Programming*, the origin of the whole subject:
--   the construction of an **intersection cut**.
--
--   Let $\bar x$ be a basic solution of the LP relaxation with basic index set $I$ and nonbasic
--   index set $J$, so that every nonbasic component vanishes, $\bar x_j = 0$ for $j \in J$. Let
--   $\bar a_{ij}$ ($i \in I$, $j \in J$) be the optimal simplex tableau's coefficients, and let
--   $r^j$ be the extreme-ray direction of the LP cone at $\bar x$ associated with $j \in J$ (see
--   the companion definition). Let $S$ be a $P_I$-free convex set containing $\bar x$ in its
--   interior. For each $j \in J$, let
--
--   $$
--   \lambda^*_j := \max\{\lambda_j \ge 0 : \bar x + \lambda_j r^j \in S\}
--   $$
--
--   be the parameter at which the extreme ray through $\bar x$ in direction $r^j$ meets the
--   boundary of $S$. Then the **intersection cut**
--
--   $$
--   \sum_{j \in J} \frac{1}{\lambda^*_j}\, x_j \;\ge\; 1
--   $$
--
--   cuts off $\bar x$ — since $\bar x_j = 0$ for every $j \in J$, the left-hand side vanishes at
--   $\bar x$ — but excludes no point of the mixed-integer feasible set $P_I$: every $x \in P_I$
--   satisfies the displayed inequality.
--
--   This is the founding construction of disjunctive programming: cutting planes derived from a
--   convex region around the current LP solution that is known to contain no feasible integer
--   point, generalizing the pure and mixed integer Gomory cuts (obtained when $S$ is a strip or a
--   wedge).
--
--   **Formalization Note.** The ambient index set $\iota$ plays the role of the full set of
--   structural and surplus variables; $I$ and $J$ partition it into basic and nonbasic indices.
--   The hypothesis `hlam_max` states that $\lambda^*_j$ is literally the greatest $t \ge 0$ for
--   which the ray point lies in $S$ (an `IsGreatest`, which already forces $\lambda^*_j \ge 0$ via
--   membership of $t = 0$ whenever $\bar x \in S$), matching the book's construction rather than
--   assuming positivity as a bare, unjustified hypothesis.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 4, Theorem 1.1

import Mathlib
import Definitions.Def_Disjunctive_IntroDuality_IntersectionCut

namespace Disjunctive.IntroDuality

/-- Theorem 1.1 (Balas §1.2, p. 4, [4]): the intersection cut derived from a `P_I`-free convex
set `S` cuts off the basic solution `x̄` but no point of `P_I`. `I`/`J` are the basic/nonbasic
index sets, `abar` the optimal simplex tableau's coefficients, and `lam j` is `λ*_j`, the
parameter at which the extreme ray of the LP cone `C(J)` through `x̄` in direction `r^j` meets
`bd(S)`. The ray is `x̄ + λ_j r^j` with `r^j` the direction vector of p. 3 (`r^j_j = 1`,
`r^j_i = -ā_{ij}` for `i ∈ I`); the book's display `x̄ - ā_j λ_j` on p. 4 names the same ray.
`P_I` lies in the LP cone `C(J) = {x : x_j ≥ 0, j ∈ J}`, since the surplus variables of `P` are
nonnegative, and that is what makes the cut valid on it. -/
theorem intersection_cut {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I J : Finset ι) (abar : ι → ι → ℝ) (xbar : ι → ℝ) (PI S : Set (ι → ℝ))
    (hPIFree : PIFree S PI xbar)
    (hxbarJ : ∀ j ∈ J, xbar j = 0)
    (hPI_cone : ∀ x ∈ PI, ∀ j ∈ J, 0 ≤ x j)
    (lam : ι → ℝ)
    (hlam_max : ∀ j ∈ J, IsGreatest {t : ℝ | xbar + t • extremeRay I abar j ∈ S} (lam j)) :
    (∑ j ∈ J, (lam j)⁻¹ * xbar j) < 1 ∧ ∀ x ∈ PI, 1 ≤ ∑ j ∈ J, (lam j)⁻¹ * x j := by sorry

end Disjunctive.IntroDuality

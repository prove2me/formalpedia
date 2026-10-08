-- Prove2me | Theorems.Thm_Disjunctive_Polymatroids_extreme_point_correspondence_v2
-- name    : Disjunctive.Polymatroids.extreme_point_correspondence_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:42.202091+00:00
-- url     : https://prove2.me/theorems/a9ab9c0b-081c-4244-a764-6f9ffb658406
-- title:
--   Proposition 13.23 — extreme points of $\Pi$ come from extreme points of $U$ (polymatroid rank functions)
-- statement:
--   This is Proposition 13.23 of Balas's *Disjunctive Programming*.
--
--   Let $r_1,r_2$ be polymatroid rank functions on $N$, let $\Pi := \{\pi\ge0:\pi x\le1\ \forall x\in P(r_1)\cup P(r_2)\}$, and let $U := \{u\ge0 : \sum_{A\subseteq N}u_Ar_i(A)\le1,\ i=1,2\}$. If $\pi$ is an extreme point of $\Pi$, then there exists an extreme point $u$ of $U$ such that
--   $$
--   \pi_j = \sum_{A\ni j}u_A \qquad (j\in N).
--   $$
--
--   **Formalization Note.** The retired version had no hypotheses on $r_1, r_2$. For arbitrary set functions an extreme point of $\Pi$ need not be the image of any $u \in U$; the counterexample was $n=1$, $r_1(\emptyset)=-1$, $r_1(N)=5$, $r_2\equiv1$. The new statement adds the standing assumption of §13.8 that both are polymatroid rank functions (`IsPolymatroidRankFunction`). Only the direction stated in the book is asserted.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §13.8, p. 231-232, Proposition 13.23

import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic

namespace Disjunctive.Polymatroids

/-- Proposition 13.23 (Balas, *Disjunctive Programming*, Springer 2018, §13.8, p. 231-232): for
polymatroid rank functions `r₁, r₂` on `N`, if `π` is an extreme point of `Π`, then there is an
extreme point `u` of `U := {u ≥ 0 : Σ_A u_A r_i(A) ≤ 1, i = 1,2}` with `π_j = Σ_{A∋j} u_A` for
every `j ∈ N`.

Correction w.r.t. the retired version: `r₁, r₂` were arbitrary set functions; the hypotheses
`hr1`, `hr2` now require them to be polymatroid rank functions, as the section assumes. -/
theorem extreme_point_correspondence_v2 {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ)
    (hr1 : IsPolymatroidRankFunction r1) (hr2 : IsPolymatroidRankFunction r2) (pi : Fin n → ℝ)
    (hpi : pi ∈ Set.extremePoints ℝ (PiSet r1 r2)) :
    ∃ u ∈ Set.extremePoints ℝ (USet r1 r2),
      ∀ j, pi j = ∑ A ∈ Finset.univ.filter (fun A => j ∈ A), u A := by sorry

end Disjunctive.Polymatroids

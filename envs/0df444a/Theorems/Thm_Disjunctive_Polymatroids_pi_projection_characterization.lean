-- Prove2me | Theorems.Thm_Disjunctive_Polymatroids_pi_projection_characterization
-- name    : Disjunctive.Polymatroids.pi_projection_characterization
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T17:13:26.538183+00:00
-- url     : https://prove2.me/theorems/74c25c7f-72d1-4a55-8ad6-9eb8c3378c9b
-- title:
--   Proposition 13.22 — Π as a projection of the u-system
-- statement:
--   This is Proposition 13.22 of Balas's *Disjunctive Programming*: the blocker-type polytope
--   $\Pi := \{\pi\ge0 : \pi x\le1\ \forall x\in P(r_1)\cup P(r_2)\}$ is exactly the projection,
--   onto the $\pi$-variables, of a polynomial-size polytope in the extended variables $u_A$
--   ($A\subseteq N$):
--   $$
--   \Pi = \mathrm{Proj}_\pi\Big\{\pi_j \le \sum_{A\ni j} u_A\ (j\in N),\ \sum_A u_A r_i(A)\le1\
--   (i=1,2),\ \pi,u\ge0\Big\}.
--   $$
--
--   The book's proof uses Edmonds's greedy formula for optimizing a linear function over a
--   polymatroid: for a fixed $\pi$, ordering coordinates so $\pi_{\sigma(1)}\ge\cdots\ge
--   \pi_{\sigma(n)}\ge0$ and setting $A^\pi_j := \{\sigma(1),\dots,\sigma(j)\}$, $\max\{\pi x :
--   x\in P(r_i)\}$ equals both a weighted sum of $r_i$ over the nested sets $A^\pi_j$ and the
--   minimum of the dual LP $\min\{\sum_A u_Ar_i(A) : \sum_{A\ni j}u_A\ge\pi_j,\ u\ge0\}$; $\pi\in
--   \Pi$ exactly when this dual system is feasible for both $i=1,2$ simultaneously.
--
--   **Formalization Note.** `PiProjSystem` states the *existence* of a witnessing `u` directly
--   (an explicit projection, matching `Proj_π{...}`'s own meaning) rather than re-deriving
--   Edmonds's greedy/dual-LP correspondence inside the statement — that correspondence is proof
--   content, not part of what the proposition itself asserts.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 231, Proposition 13.22

import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic

namespace Disjunctive.Polymatroids

/-- Proposition 13.22 (Balas §13.8, p. 231): `Π` equals its projection system: `Π = Proj_π{π_j ≤
Σ_{A∋j} u_A for j∈N, Σ_A u_Ar_i(A)≤1 for i=1,2, π≥0, u_A≥0 for all A⊆N}`. -/
theorem pi_projection_characterization {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ) :
    PiSet r1 r2 = PiProjSystem r1 r2 := by sorry

end Disjunctive.Polymatroids

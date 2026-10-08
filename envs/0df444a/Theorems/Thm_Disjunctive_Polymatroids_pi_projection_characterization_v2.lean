-- Prove2me | Theorems.Thm_Disjunctive_Polymatroids_pi_projection_characterization_v2
-- name    : Disjunctive.Polymatroids.pi_projection_characterization_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:56.862734+00:00
-- url     : https://prove2.me/theorems/bf071f92-54c0-431d-9d75-43d6f14bf4c9
-- title:
--   Proposition 13.22 — $\Pi$ as a projection, for polymatroid rank functions $r_1,r_2$
-- statement:
--   This is Proposition 13.22 of Balas's *Disjunctive Programming*.
--
--   Let $r_1, r_2 : 2^N \to \mathbb R$ be polymatroid rank functions ($r(\emptyset)=0$, nondecreasing, submodular), $P(r_i) := \{x\in\mathbb R^n_+ : x(A)\le r_i(A)\ \forall A\subseteq N\}$, and $\Pi := \{\pi\ge0 : \pi x\le1 \text{ for all } x\in P(r_1)\cup P(r_2)\}$. Then
--   $$
--   \Pi = \mathrm{Proj}_\pi\Big\{(\pi,u) : \pi_j\le\sum_{A\ni j}u_A\ (j\in N),\ \sum_{A\subseteq N}u_Ar_i(A)\le1\ (i=1,2),\ \pi\ge0,\ u\ge0\Big\}.
--   $$
--
--   **Formalization Note.** The retired version had no hypotheses on $r_1, r_2$. For arbitrary set functions there need not be a single multiplier vector $u$ that works for both functions, and the equality fails: with $n=1$, $r_1(\emptyset)=-1$, $r_1(N)=5$, $r_2\equiv1$, $\pi=(1)$. The new statement adds the standing assumption of §13.8 that both are polymatroid rank functions (`IsPolymatroidRankFunction`, already in the definition module). Under it, the greedy dual solution $u$ depends only on the order of $\pi$ and therefore serves both functions at once.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §13.8, p. 231, Proposition 13.22

import Mathlib
import Definitions.Def_Disjunctive_Polymatroids_Basic

namespace Disjunctive.Polymatroids

/-- Proposition 13.22 (Balas, *Disjunctive Programming*, Springer 2018, §13.8, p. 231): for
polymatroid rank functions `r₁, r₂` on `N` (the standing assumption of §13.8: `r(∅) = 0`,
nondecreasing, submodular), `Π := {π ≥ 0 : πx ≤ 1 for x ∈ P(r₁) ∪ P(r₂)}` equals the projection
onto `π` of `{(π,u) : π_j ≤ Σ_{A∋j} u_A (j ∈ N), Σ_A u_A r_i(A) ≤ 1 (i = 1,2), π, u ≥ 0}`.

Correction w.r.t. the retired version: `r₁, r₂` were arbitrary set functions; the hypotheses
`hr1`, `hr2` now require them to be polymatroid rank functions, as the section assumes. -/
theorem pi_projection_characterization_v2 {n : ℕ} (r1 r2 : Finset (Fin n) → ℝ)
    (hr1 : IsPolymatroidRankFunction r1) (hr2 : IsPolymatroidRankFunction r2) :
    PiSet r1 r2 = PiProjSystem r1 r2 := by sorry

end Disjunctive.Polymatroids

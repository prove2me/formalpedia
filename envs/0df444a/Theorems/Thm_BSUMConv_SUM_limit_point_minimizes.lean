-- Prove2me | Theorems.Thm_BSUMConv_SUM_limit_point_minimizes
-- name    : BSUMConv.SUM.limit_point_minimizes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:33.069913+00:00
-- url     : https://prove2.me/theorems/465acca6-1ebe-4f57-abda-bb80c6d083f7
-- title:
--   Proof of Theorem 1, p. 7 — a limit point z of a SUM run lies in 𝒳 and minimizes u(·, z): u(z, z) ≤ u(x, z) for all x ∈ 𝒳
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^m$ be closed, $f:\mathbb R^m\to\mathbb R$, and let $u$ satisfy (A1) $u(y,y)=f(y)$ on $\mathcal X$, (A2) $u(x,y)\ge f(x)$ on $\mathcal X\times\mathcal X$ and (A4) $u$ continuous on $\mathcal X\times\mathcal X$. Let $x^0,x^1,\dots$ be a run of the SUM algorithm and let $z$ be a limit point of the sequence, i.e. the limit of some subsequence $x^{r_j}$. Then $z\in\mathcal X$ and
--   $$
--   u(z,z)\le u(x,z)\qquad\forall\,x\in\mathcal X .
--   $$
--
--   The limit point thus solves the subproblem it would itself generate. Together with the first-order condition for a minimiser over a convex set and (A3) this yields stationarity in Theorem 1.
--
--   **Formalization Note** "Limit point" is a cluster point of the sequence (`MapClusterPt z atTop x`), not a limit of the whole sequence. The conclusion $z\in\mathcal X$, implicit on the page, is stated explicitly; it follows from closedness of $\mathcal X$. Convexity of $\mathcal X$ and (A3) are not used here and are not hypotheses.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, p. 7, proof of Theorem 1, the display u(z, z) ≤ u(x, z), ∀ x ∈ 𝒳

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_SUM_Setting

namespace BSUMConv.SUM

open Filter Topology

/-- Proof of Theorem 1, p. 7: if `z` is a limit point of a SUM run, then `z ∈ 𝒳` and
`u(z, z) ≤ u(x, z)` for all `x ∈ 𝒳`. -/
theorem limit_point_minimizes {m : ℕ} (Xset : Set (EuclideanSpace ℝ (Fin m)))
    (hclosed : IsClosed Xset)
    (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (u : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hA1 : AssumptionA1 Xset f u) (hA2 : AssumptionA2 Xset f u) (hA4 : AssumptionA4 Xset u)
    (x : ℕ → EuclideanSpace ℝ (Fin m)) (hx : IsSUMRun Xset u x)
    (z : EuclideanSpace ℝ (Fin m)) (hz : MapClusterPt z atTop x) :
    z ∈ Xset ∧ ∀ y ∈ Xset, u z z ≤ u y z := by sorry

end BSUMConv.SUM

-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_plane_open_book_of_page_foliation
-- name    : FiniteEnergyPlane.exists_plane_open_book_of_page_foliation
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-04T15:52:39.897203+00:00
-- url     : https://prove2.me/theorems/c2cb4f25-15f1-4989-bdce-186383a5b1e2
-- title:
--   From a foliation over an interval to a periodic family of fast planes
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T_P)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ ($P$ may be degenerate unless stated otherwise). Let $y$ be a Reeb trajectory, $\gamma\in\mathbb{R}$, $l\ge1$, $L,\delta>0$, and let $U$ satisfy `IsPageFoliation H J P γ y l L δ U`. Then there is a map $W$ with `IsPlaneOpenBook H J P l W`.
--
--   **Formalization Note** $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`, the index of the linearized flow along $P$ in the global frame of $\xi$. Hryniewicz writes $\mu(\tilde u)=k\ge3$ and restricts to $\Lambda_k$; on a strictly star-shaped level $\xi$ has a global frame, which extends over every capping disk, so the index depends only on $P$, $\Lambda_k=\Lambda$, and the condition is not restated. Hryniewicz's map is $L$-periodic on $\mathbb{R}/L\mathbb{Z}\times\mathbb{C}$, and here the period is normalized to $1$. The slices of $W$ are not required to lie in any $\Lambda(\{y(t)\},P)$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Section 7.2.2, formula (108)

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), § 7.2.2, (108). Let `P` be a periodic Reeb orbit of Conley–Zehnder
index at least `3`, `y` a Reeb trajectory and `U` a `C^l` family (`l ≥ 1`) with `IsPageFoliation`
on an interval of length `L` (with margin `δ`). Then there is a map satisfying `IsPlaneOpenBook`
at the same regularity `l`. -/
theorem exists_plane_open_book_of_page_foliation (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (L δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (U : ℝ × ℂ → V 1)
    (hU : IsPageFoliation H J P γ y l L δ U) :
    ∃ W : ℝ × ℂ → V 1, IsPlaneOpenBook H J P l W := by
  sorry

end FiniteEnergyPlane

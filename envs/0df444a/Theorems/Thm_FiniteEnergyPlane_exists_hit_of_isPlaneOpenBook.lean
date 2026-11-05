-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_hit_of_isPlaneOpenBook
-- name    : FiniteEnergyPlane.exists_hit_of_isPlaneOpenBook
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-04T15:52:55.684224+00:00
-- url     : https://prove2.me/theorems/39371183-232f-425e-b832-afe7472b4c66
-- title:
--   Every trajectory off $P$ meets every leaf at arbitrarily large and arbitrarily negative times
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T_P)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ ($P$ may be degenerate unless stated otherwise). Suppose every periodic Reeb orbit of period at most $T_P$ is nondegenerate, let $l\ge1$ and let $U$ satisfy `IsPlaneOpenBook H J P l U`. If $y$ is a Reeb trajectory with $y(0)\notin x(\mathbb{R})$, then for all $\theta,n\in\mathbb{R}$ there are $t>n$ and $t'<n$ with $y(t),y(t')\in\mathrm{proj}(U(\theta,\mathbb{C}))$.
--
--   **Formalization Note** Periods are those of `ReebOrbit H` (not necessarily minimal, so multiple covers count). $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`, the index of the linearized flow along $P$ in the global frame of $\xi$. Hryniewicz writes $\mu(\tilde u)=k\ge3$ and restricts to $\Lambda_k$; on a strictly star-shaped level $\xi$ has a global frame, which extends over every capping disk, so the index depends only on $P$, $\Lambda_k=\Lambda$, and the condition is not restated. The statement holds for an arbitrary map with `IsPlaneOpenBook`, not only for Hryniewicz's map (108).
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Section 7.2.3

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), § 7.2.3. Let `P` be a periodic Reeb orbit of Conley–Zehnder index
at least `3` such that every periodic orbit of period at most `P.T` is nondegenerate, and let `U`
satisfy `IsPlaneOpenBook` with `l ≥ 1`. Every Reeb trajectory `y` with `y 0 ∉ x(ℝ)` meets every leaf
`pageMap H U (θ, ·)` at times larger than any given `n` and at times smaller than any given `n`. -/
theorem exists_hit_of_isPlaneOpenBook (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (hnd : ∀ Q : ReebOrbit H, Q.T ≤ P.T → Q.IsNondegenerate)
    (l : ℕ) (hl : 1 ≤ l) (U : ℝ × ℂ → V 1) (hU : IsPlaneOpenBook H J P l U)
    (y : ℝ → V 1) (hy : IsReebTrajectory H y) (hy₀ : y 0 ∉ Set.range P.x) (θ n : ℝ) :
    (∃ t > n, y t ∈ Set.range (fun z => pageMap H U (θ, z))) ∧
      (∃ t < n, y t ∈ Set.range (fun z => pageMap H U (θ, z))) := by
  sorry

end FiniteEnergyPlane

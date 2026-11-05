-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_contDiff_rotation_gauge
-- name    : FiniteEnergyPlane.exists_contDiff_rotation_gauge
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-04T15:47:59.753024+00:00
-- url     : https://prove2.me/theorems/ad35f0be-53bd-4cf4-a4de-2623dc6faa8f
-- title:
--   Two families along a trajectory differ by a $C^l$ rotation
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T_P)$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ ($P$ may be degenerate unless stated otherwise). Let $y$ be a Reeb trajectory, $\gamma\in\mathbb{R}$, $l\ge1$, let $I,I'\subset\mathbb{R}$ be open intervals, and let $U$ on $I\times\mathbb{C}$ and $W$ on $I'\times\mathbb{C}$ be $C^l$ families with `IsPageFamilyOn`. Then there is a function $\theta$, of class $C^l$ on $I\cap I'$, such that $U(t,z)=W(t,e^{2\pi i\theta(t)}z)$ for all $t\in I\cap I'$ and $z\in\mathbb{C}$.
--
--   **Formalization Note** An open interval of $\mathbb{R}$ is an open convex set, possibly unbounded or empty. $\mu_{CZ}(P)\ge3$ is `P.IsCZAtLeast 3`, the index of the linearized flow along $P$ in the global frame of $\xi$. Hryniewicz writes $\mu(\tilde u)=k\ge3$ and restricts to $\Lambda_k$; on a strictly star-shaped level $\xi$ has a global frame, which extends over every capping disk, so the index depends only on $P$, $\Lambda_k=\Lambda$, and the condition is not restated.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 7.4

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Lemma 7.4. Let `P` be a periodic Reeb orbit of Conley–Zehnder
index at least `3` and `y` a Reeb trajectory. Let `U` and `W` be `C^l` families (`l ≥ 1`) along `y`
on `I × ℂ` and `I' × ℂ`, for open intervals `I`, `I'`. Then there is a function `θ`, of class `C^l`
on `I ∩ I'`, with `U(t, z) = W(t, e^{2π i θ(t)} z)` for all `t ∈ I ∩ I'` and all `z`. -/
theorem exists_contDiff_rotation_gauge (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I I' : Set ℝ) (hI : IsOpen I) (hI' : IsOpen I')
    (hIc : Convex ℝ I) (hIc' : Convex ℝ I') (U W : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (hW : IsPageFamilyOn H J P γ y l I' W) :
    ∃ θ : ℝ → ℝ, ContDiffOn ℝ l θ (I ∩ I') ∧ ∀ t ∈ I ∩ I', ∀ z,
      U (t, z) = W (t, Complex.exp (((2 * π * θ t : ℝ) : ℂ) * Complex.I) * z) := by
  sorry

end FiniteEnergyPlane

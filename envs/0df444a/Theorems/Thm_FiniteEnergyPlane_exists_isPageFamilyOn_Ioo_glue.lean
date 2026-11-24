-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_isPageFamilyOn_Ioo_glue
-- name    : FiniteEnergyPlane.exists_isPageFamilyOn_Ioo_glue
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-23T22:36:25.122591+00:00
-- url     : https://prove2.me/theorems/c32b79f5-fe1f-49c3-bb86-280b926b89c5
-- title:
--   Gluing two page families along a Reeb trajectory
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P$ be a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$ and $y$ a Reeb trajectory. Let $U$, $W$ be $C^l$ families ($l\ge1$) along $y$ on $(a,s)\times\mathbb{C}$ and $(c,d)\times\mathbb{C}$, and let $m\in(a,s)\cap(c,d)$. Then there is a $C^l$ family along $y$ on $(a,d)\times\mathbb{C}$ that equals $U$ on $(a,m]\times\mathbb{C}$.
--
--   Reusable for extending families of pages in time.
--
--   **Formalization Note** `IsPageFamilyOn H J P γ y l I U` says that $U$ is $C^l$ on $I\times\mathbb{C}$ and $U(t,\cdot)\in\Lambda(\{y(t)\},P)$ for $t\in I$; $\Lambda(K,P)$ is `embeddedFastPlaneSet H J P K γ`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7.1

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `P` be a periodic Reeb orbit of Conley–Zehnder index at least `3` and `y` a Reeb trajectory.
Let `U` and `W` be `C^l` families (`l ≥ 1`) along `y` on `(a, s) × ℂ` and `(c, d) × ℂ`, and let `m` lie
in both `(a, s)` and `(c, d)`. Then there is a `C^l` family along `y` on `(a, d) × ℂ` that equals `U`
on `(a, m] × ℂ`. -/
theorem exists_isPageFamilyOn_Ioo_glue (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (a s c d m : ℝ) (U W : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l (Set.Ioo a s) U)
    (hW : IsPageFamilyOn H J P γ y l (Set.Ioo c d) W)
    (hm : m ∈ Set.Ioo a s) (hm' : m ∈ Set.Ioo c d) :
    ∃ U' : ℝ × ℂ → V 1, IsPageFamilyOn H J P γ y l (Set.Ioo a d) U' ∧
      ∀ t ∈ Set.Ioc a m, ∀ z, U' (t, z) = U (t, z) := by
  sorry

end FiniteEnergyPlane

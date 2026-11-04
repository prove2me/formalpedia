-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isSeqCompact_fastPlaneSet
-- name    : FiniteEnergyPlane.isSeqCompact_fastPlaneSet
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-03T16:26:24.491569+00:00
-- url     : https://prove2.me/theorems/0146b629-d3c3-4d56-bb1e-a266072898c6
-- title:
--   Compactness of fast finite-energy planes
-- statement:
--   Let $H_0:\mathbb{R}^4\to\mathbb{R}$ have a strictly star-shaped level (in the sense of `HryniewiczCriterion`), $H$ the same function on $V=\mathbb{R}^{2\cdot(1+1)}$, $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$ and $P$ a periodic Reeb orbit of $H$. Suppose every periodic orbit of `HryniewiczCriterion` of action at most $T_P$ is nondegenerate and has $\mu_{CZ}\ge3$. Let $\gamma>0$ be smaller than every period at most $T_P$ and than every difference of two distinct such periods, and let $K\subset\mathbb{R}^4\setminus\{0\}$ be compact with $K\cap(\mathbb{R}\times x(\mathbb{R}))=\emptyset$, where $P=(x,T_P)$. Then $\Theta(K,P)$ is sequentially compact in $C^\infty_{loc}(\mathbb{C},\mathbb{R}^4)$.
--
--   **Formalization Note** The orbit hypotheses have the form of `exists_transverse_disk_open_book_of_approx` at a single level: for every `R : PeriodicOrbit H₀` and `Y` with `IsLinearizedFlow H₀ R.x Y` and action $\int_0^{T_R}\lambda_0(\dot x)\le T_P$, `linearizedXiPath H₀ R Y 1` fixes no nonzero vector and `3 ≤ czIndexOfPath (linearizedXiPath H₀ R Y)`. $K\cap(\mathbb{R}\times x(\mathbb{R}))=\emptyset$ is `∀ y ∈ K, proj H y ∉ Set.range P.x`. $\Theta(K,P)$ is `fastPlaneSet H J P K γ`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Theorem 2.2 (2); U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 3.10

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz (Trans. AMS 2012), Theorem 2.2 (2), for `Θ`; Hryniewicz (J. Symplectic Geom. 2014),
Theorem 3.10. Let `S = H⁻¹(1) ⊂ ℝ⁴` be strictly star-shaped and `P` a periodic Reeb orbit. Suppose
every periodic orbit of `HryniewiczCriterion` of action at most `P.T` is nondegenerate with
Conley–Zehnder index at least `3` (as in `exists_transverse_disk_open_book_of_approx`), let
`0 < γ` be smaller than every period at most `P.T` and every difference of two distinct such
periods, and let `K ⊂ V 1 \ {0}` be a compact set disjoint from the cone `ℝ × x(ℝ)` over the image
of `P`. Then `fastPlaneSet H J P K γ` is sequentially compact in `C^∞_loc(ℂ, V 1)`. -/
theorem isSeqCompact_fastPlaneSet (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J → ∀ P : ReebOrbit H,
    (∀ (R : HryniewiczCriterion.PeriodicOrbit H₀)
      (Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4)),
      HryniewiczCriterion.IsLinearizedFlow H₀ R.x Y →
      (∫ t in (0 : ℝ)..R.T, HryniewiczCriterion.liouvilleForm (R.x t) (deriv R.x t)) ≤ P.T →
      ∀ v : Fin 2 → ℝ, (HryniewiczCriterion.linearizedXiPath H₀ R Y 1).mulVec v = v → v = 0) →
    (∀ (R : HryniewiczCriterion.PeriodicOrbit H₀)
      (Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4)),
      HryniewiczCriterion.IsLinearizedFlow H₀ R.x Y →
      (∫ t in (0 : ℝ)..R.T, HryniewiczCriterion.liouvilleForm (R.x t) (deriv R.x t)) ≤ P.T →
      3 ≤ HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath H₀ R Y)) →
    ∀ γ : ℝ, 0 < γ → (∀ Q : ReebOrbit H, Q.T ≤ P.T → γ < Q.T) →
    (∀ Q₁ Q₂ : ReebOrbit H, Q₁.T ≤ P.T → Q₂.T ≤ P.T → Q₁.T ≠ Q₂.T → γ < |Q₁.T - Q₂.T|) →
    ∀ K : Set (V 1), IsCompact K → (0 : V 1) ∉ K → (∀ y ∈ K, proj H y ∉ Set.range P.x) →
    IsSeqCompactCInftyLoc (fastPlaneSet H J P K γ) := by
  sorry

end FiniteEnergyPlane

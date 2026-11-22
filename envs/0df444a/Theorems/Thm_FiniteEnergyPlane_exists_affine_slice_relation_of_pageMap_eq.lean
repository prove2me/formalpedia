-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_affine_slice_relation_of_pageMap_eq
-- name    : FiniteEnergyPlane.exists_affine_slice_relation_of_pageMap_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:30:19.539538+00:00
-- url     : https://prove2.me/theorems/a86dec5f-a5ae-4c62-be94-72accc393fd9
-- title:
--   Two slices of a page family meeting in S are related by a contracting affine change
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be strictly star-shaped, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, $P$ a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$, $y$ a curve, $\gamma\in\mathbb{R}$, $I\subseteq\mathbb{R}$, and $U$ a family on $I\times\mathbb{C}$ with $U(t,\cdot)\in\Lambda(\{y(t)\},P)$ for every $t\in I$. If $\mathrm{pr}_S U(s,z)=\mathrm{pr}_S U(s',z')$ for some $s,s'\in I$ and $z,z'\in\mathbb{C}$, then, after possibly exchanging $s$ and $s'$ (call the resulting pair $\sigma,\sigma'$), there are $c\in\mathbb{R}$ and $A,B\in\mathbb{C}$ with $A\neq0$, $|A|\le1$ and
--   $$U(\sigma,Aw+B)=e^{2c}\,U(\sigma',w)\qquad\text{for all }w\in\mathbb{C}.$$
--
--   Two leaves of such a family that meet in $S$ are reparametrizations of each other, up to an $\mathbb{R}$-translation in the symplectization, and the order of the two leaves can be chosen so that the affine factor does not expand. It is used for the local injectivity of the projection of a family (Hryniewicz 2012, Lemma 7.2).
--
--   **Formalization Note** $\Lambda(\{y_0\},P)$ is `embeddedFastPlaneSet H J P {y₀} γ`; the family conditions are `IsPageFamilyOn H J P γ y l I U` (only the slice membership is used); $\mathrm{pr}_S\circ U$ is `pageMap H U`; $e^{2c}\,U$ is the translation `shiftA c` of the symplectization written out. The exchange is the disjunction `(σ = s ∧ σ' = s') ∨ (σ = s' ∧ σ' = s)`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.2

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `U` be a `C^l` family on `I × ℂ` with `U(t, ·) ∈ Λ({y t}, P)` for `t ∈ I`, where
`μ_CZ(P) ≥ 3`. If `pageMap H U (s, z) = pageMap H U (s', z')` with `s, s' ∈ I`, then, after
possibly exchanging `s` and `s'` (giving `σ, σ'`), there are `c ∈ ℝ` and `A, B ∈ ℂ` with
`A ≠ 0`, `|A| ≤ 1` and `U(σ, A w + B) = e^{2c} U(σ', w)` for all `w`. -/
theorem exists_affine_slice_relation_of_pageMap_eq (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1)
    (l : ℕ) (I : Set ℝ) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U) (s s' : ℝ) (hs : s ∈ I) (hs' : s' ∈ I) (z z' : ℂ)
    (he : pageMap H U (s, z) = pageMap H U (s', z')) :
    ∃ (σ σ' c : ℝ) (A B : ℂ), ((σ = s ∧ σ' = s') ∨ (σ = s' ∧ σ' = s)) ∧ A ≠ 0 ∧ ‖A‖ ≤ 1 ∧
      ∀ w, U (σ, A * w + B) = Real.exp (2 * c) • U (σ', w) := by
  sorry

end FiniteEnergyPlane

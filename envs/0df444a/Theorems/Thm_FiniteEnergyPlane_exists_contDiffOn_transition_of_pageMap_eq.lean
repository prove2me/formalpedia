-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_contDiffOn_transition_of_pageMap_eq
-- name    : FiniteEnergyPlane.exists_contDiffOn_transition_of_pageMap_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T14:04:12.339533+00:00
-- url     : https://prove2.me/theorems/f3286e72-0557-4da2-88ee-4b77c90fff69
-- title:
--   $C^l$ transition between two times of a page family with a common leaf
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P$ be a periodic Reeb orbit with $\mu_{CZ}(P)\ge3$, $y$ a Reeb trajectory, $I\subseteq\mathbb{R}$ open and $U$ a $C^l$ family ($l\ge1$) along $y$ on $I\times\mathbb{C}$ whose map $\mathrm{proj}_H\circ U$ has injective derivative and is positive against the Reeb field. If the leaves at $t_0,t_1\in I$ share a point of $S$, then there are $\eta>0$ with $(t_0-\eta,t_0+\eta)\subseteq I$ and $C^l$ functions $\beta,c$ (real) and $A,B$ (complex) on this interval with $\beta(t_0)=t_1$, $\beta\in I$, $\beta'>0$, $A\neq0$ and $$U(s,z)=e^{2c(s)}\,U(\beta(s),A(s)z+B(s))\quad\text{for all }z\in\mathbb{C}.$$
--
--   It compares the parametrizations of a page family before and after a return to the same leaf; reusable for gluing families of pages.
--
--   **Formalization Note** The family is `IsPageFamilyOn H J P γ y l I U`, $\mathrm{proj}_H\circ U$ is `pageMap H U`, positivity is `IsReebPositiveAt`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7.2.2

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `P` have Conley–Zehnder index at least `3`, `y` a Reeb trajectory, `I ⊆ ℝ` open and `U` a
`C^l` family (`l ≥ 1`) along `y` on `I × ℂ` such that `pageMap H U` has injective derivative and is
positive against the Reeb field. If the leaves at `t₀, t₁ ∈ I` share a point, then near `t₀` there
are `C^l` functions `β, c, A, B` with `β(t₀) = t₁`, `β' > 0`, `A ≠ 0` and
`U(s, z) = e^{2 c(s)} U(β(s), A(s) z + B(s))`. -/
theorem exists_contDiffOn_transition_of_pageMap_eq (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (I : Set ℝ) (hI : IsOpen I) (U : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l I U)
    (hinj : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), Function.Injective (fderiv ℝ (pageMap H U) p))
    (hpos : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), IsReebPositiveAt H U p)
    (t₀ t₁ : ℝ) (ht₀ : t₀ ∈ I) (ht₁ : t₁ ∈ I) (z₀ z₁ : ℂ)
    (h01 : pageMap H U (t₀, z₀) = pageMap H U (t₁, z₁)) :
    ∃ η > 0, ball t₀ η ⊆ I ∧ ∃ (β c : ℝ → ℝ) (A B : ℝ → ℂ),
      ContDiffOn ℝ l β (ball t₀ η) ∧ ContDiffOn ℝ l c (ball t₀ η) ∧
      ContDiffOn ℝ l A (ball t₀ η) ∧ ContDiffOn ℝ l B (ball t₀ η) ∧ β t₀ = t₁ ∧
      ∀ s ∈ ball t₀ η, β s ∈ I ∧ 0 < deriv β s ∧ A s ≠ 0 ∧
        ∀ z, U (s, z) = Real.exp (2 * c s) • U (β s, A s * z + B s) := by
  sorry

end FiniteEnergyPlane

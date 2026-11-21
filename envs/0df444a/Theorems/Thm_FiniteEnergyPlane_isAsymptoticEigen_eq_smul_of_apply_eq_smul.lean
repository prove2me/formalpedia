-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isAsymptoticEigen_eq_smul_of_apply_eq_smul
-- name    : FiniteEnergyPlane.isAsymptoticEigen_eq_smul_of_apply_eq_smul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T23:45:40.290957+00:00
-- url     : https://prove2.me/theorems/f98a2d7e-8028-425e-9ba4-005da32a8b68
-- title:
--   Parallel asymptotic eigenvectors with equal winding are proportional
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T)$ a periodic Reeb orbit with asymptotic operator $A_P$. Let $e_1,e_2$ be eigenvectors of $A_P$, for eigenvalues $\mu_1,\mu_2$, with the same winding number $k$ in the global frame of $\xi$. If $e_1(\sigma)=c\,e_2(\sigma)$ for some $\sigma,c\in\mathbb{R}$, then
--   $$\mu_1=\mu_2\qquad\text{and}\qquad e_1(t)=c\,e_2(t)\ \text{ for all } t\in\mathbb{R}.$$
--
--   Role: rigidity of eigenvectors of equal winding; used to compare the leading asymptotic eigenvectors of two planes over the same orbit.
--
--   **Formalization Note** Eigenvectors are `IsAsymptoticEigen J P μ e`; winding in the global frame is `HasXiLoopWind P e k`. $P$ need not be prime or nondegenerate, and the eigenspace may be two-dimensional.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.23; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II, Geom. Funct. Anal. 5 (1995), 270–328, Lemma 3.5

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Two eigenvectors `e₁, e₂` of the asymptotic operator `A_P` of a periodic Reeb orbit on a
strictly star-shaped level in `ℝ⁴`, with the same winding number in the global frame of `ξ`,
that are parallel at one point, `e₁(σ) = c e₂(σ)`, have the same eigenvalue and satisfy
`e₁ = c e₂` everywhere. -/
theorem isAsymptoticEigen_eq_smul_of_apply_eq_smul (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) {μ₁ μ₂ : ℝ} {e₁ e₂ : ℝ → V 1}
    (h₁ : IsAsymptoticEigen J P μ₁ e₁) (h₂ : IsAsymptoticEigen J P μ₂ e₂)
    {k : ℤ} (hk₁ : HasXiLoopWind P e₁ k) (hk₂ : HasXiLoopWind P e₂ k) {σ c : ℝ}
    (h : e₁ σ = c • e₂ σ) : μ₁ = μ₂ ∧ ∀ t, e₁ t = c • e₂ t := by
  sorry

end FiniteEnergyPlane

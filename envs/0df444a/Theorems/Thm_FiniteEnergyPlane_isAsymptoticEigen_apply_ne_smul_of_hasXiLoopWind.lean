-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isAsymptoticEigen_apply_ne_smul_of_hasXiLoopWind
-- name    : FiniteEnergyPlane.isAsymptoticEigen_apply_ne_smul_of_hasXiLoopWind
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T23:17:44.041231+00:00
-- url     : https://prove2.me/theorems/dbb5380f-c85a-4fec-b157-e218ac2f3efe
-- title:
--   Asymptotic eigenvectors with equal winding are pointwise independent
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T)$ a periodic Reeb orbit with asymptotic operator $A_P$. Let $e_1,e_2$ be eigenvectors of $A_P$ for eigenvalues $\mu_1\neq\mu_2$ that have the same winding number $k$ in the global frame of $\xi$. Then $e_1$ and $e_2$ are pointwise linearly independent:
--   $$e_2(t)\neq c\,e_1(t)\qquad\text{for all } t\in\mathbb{R},\ c\in\mathbb{R}.$$
--
--   Role: the version along $\xi|_P$ of the pointwise independence of eigenfunctions with equal winding (HWZ95, Lemma 3.5), in the form used to compare the asymptotic eigenvectors of two planes over the same orbit.
--
--   **Formalization Note** Eigenvectors are `IsAsymptoticEigen J P μ e` (smooth $1$-periodic sections of $\xi$ along $t\mapsto x(Tt)$, not identically zero); winding in the global frame is `HasXiLoopWind P e k`. $P$ need not be prime or nondegenerate.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.23; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II, Geom. Funct. Anal. 5 (1995), 270–328, Lemma 3.5

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Eigenvectors of the asymptotic operator `A_P` of a periodic Reeb orbit on a strictly
star-shaped level in `ℝ⁴`, for two distinct eigenvalues and with the same winding number in the
global frame of `ξ`, are pointwise linearly independent: `e₂(t) ≠ c e₁(t)` for all `t, c`. -/
theorem isAsymptoticEigen_apply_ne_smul_of_hasXiLoopWind (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) {μ₁ μ₂ : ℝ} (hμ : μ₁ ≠ μ₂) {e₁ e₂ : ℝ → V 1}
    (he₁ : IsAsymptoticEigen J P μ₁ e₁) (he₂ : IsAsymptoticEigen J P μ₂ e₂) {k : ℤ}
    (hk₁ : HasXiLoopWind P e₁ k) (hk₂ : HasXiLoopWind P e₂ k) (t c : ℝ) : e₂ t ≠ c • e₁ t := by
  sorry

end FiniteEnergyPlane

-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isFastPlane_exp_smul_comp_affine
-- name    : FiniteEnergyPlane.isFastPlane_exp_smul_comp_affine
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T13:42:34.103681+00:00
-- url     : https://prove2.me/theorems/cbc7471b-702c-46e0-81a4-1ba7548843f6
-- title:
--   Complex affine reparametrizations and translations of planes of $\Lambda(K,P)$
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P$ be a periodic Reeb orbit, $K\subseteq\mathbb{R}^4$ and $u\in\Lambda(K,P)$. For all $c\in\mathbb{R}$ and $A,B\in\mathbb{C}$ with $A\neq0$, the map $z\mapsto e^{2c}u(Az+B)$ is an embedded fast finite-energy plane asymptotic to $P$ at $\infty$.
--
--   Reusable whenever families of planes are reparametrized leafwise.
--
--   **Formalization Note** $\Lambda(K,P)$ is `embeddedFastPlaneSet H J P K γ`; multiplication by $e^{2c}$ is the translation by $c$ in the $\mathbb{R}$-direction of the symplectization. The normalizations at $0$ and of the $d\lambda$-energy are not asserted for the new plane.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7.2.2

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If `u ∈ Λ(K, P)`, then for all `c ∈ ℝ` and `A, B ∈ ℂ` with `A ≠ 0` the map
`z ↦ e^{2c} u(A z + B)` is an embedded fast finite-energy plane asymptotic to `P` at `∞`. -/
theorem isFastPlane_exp_smul_comp_affine (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (K : Set (V 1)) (γ : ℝ) (u : ℂ → V 1) (hu : u ∈ embeddedFastPlaneSet H J P K γ)
    (c : ℝ) (A B : ℂ) (hA : A ≠ 0) :
    IsFastPlane H J (fun z => Real.exp (2 * c) • u (A * z + B)) ∧
      IsNondegenerateEnd H (fun z => Real.exp (2 * c) • u (A * z + B)) cylInf P 1 ∧
      IsEmbeddedPlane (fun z => Real.exp (2 * c) • u (A * z + B)) := by
  sorry

end FiniteEnergyPlane

-- Prove2me | Theorems.Thm_FiniteEnergyPlane_comp_exp_mul_mem_embeddedFastPlaneSet
-- name    : FiniteEnergyPlane.comp_exp_mul_mem_embeddedFastPlaneSet
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-23T22:32:05.89563+00:00
-- url     : https://prove2.me/theorems/001e2466-f148-4b80-89c4-4098d11384de
-- title:
--   The set $\Lambda(K,P)$ is invariant under rotations of the domain
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $P$ be a periodic Reeb orbit, $K\subseteq\mathbb{R}^4$ and $u\in\Lambda(K,P)$. Then $z\mapsto u(e^{2\pi i\alpha}z)$ lies in $\Lambda(K,P)$ for every $\alpha\in\mathbb{R}$.
--
--   It complements Lemma 7.1, by which planes of $\Lambda(\{y_0\},P)$ differ only by such rotations.
--
--   **Formalization Note** $\Lambda(K,P)$ is `embeddedFastPlaneSet H J P K γ`: embedded fast planes asymptotic to $P$ at $\infty$, with $u(0)\in K$ and $d\lambda$-energy $\gamma$ on $\{|z|>1\}$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7.1

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The set `Λ(K, P)` is invariant under rotations of the domain: if `u ∈ Λ(K, P)`, then
`z ↦ u (e^{2πiα} z)` lies in `Λ(K, P)` for every real `α`. -/
theorem comp_exp_mul_mem_embeddedFastPlaneSet (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (K : Set (V 1)) (γ : ℝ) (u : ℂ → V 1) (hu : u ∈ embeddedFastPlaneSet H J P K γ) (α : ℝ) :
    (fun z => u (Complex.exp (((2 * π * α : ℝ) : ℂ) * Complex.I) * z)) ∈
      embeddedFastPlaneSet H J P K γ := by
  sorry

end FiniteEnergyPlane

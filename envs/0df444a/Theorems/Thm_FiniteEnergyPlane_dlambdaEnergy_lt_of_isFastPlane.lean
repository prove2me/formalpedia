-- Prove2me | Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_lt_of_isFastPlane
-- name    : FiniteEnergyPlane.dlambdaEnergy_lt_of_isFastPlane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T11:04:50.021886+00:00
-- url     : https://prove2.me/theorems/b4ad5756-0002-4bf2-ab8f-4a9a4b64358c
-- title:
--   Strict monotonicity of the dλ-energy of a fast plane outside a disk
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with a compatible complex structure $J$ on $\xi$, and let $u:\mathbb{C}\to\mathbb{R}\times S$ be a fast finite-energy plane (`IsFastPlane`). Let $0\le r_1<r_2$ and suppose $\int_{\{|z|>r_1\}}u^*d\lambda<\infty$. Then
--   $$\int_{\{|z|>r_2\}}u^*d\lambda\;<\;\int_{\{|z|>r_1\}}u^*d\lambda .$$
--
--   Role: on a fast plane the $d\lambda$-energy outside a disk is a strictly decreasing function of the radius. In particular a normalization $\int_{\{|z|>1\}}u^*d\lambda=\gamma$ determines the scale of the domain parametrization.
--
--   **Formalization Note** The energies are `dlambdaEnergy H {z | r < ‖z‖} u` with values in $[0,\infty]$; the finiteness hypothesis is stated for the larger set.
-- source:
--   Finite-energy planes; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 7.1

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u` be a fast finite-energy plane and `0 ≤ r₁ < r₂`. If the `dλ`-energy of `u` on
`{z | r₁ < ‖z‖}` is finite, then the `dλ`-energy of `u` on `{z | r₂ < ‖z‖}` is strictly smaller. -/
theorem dlambdaEnergy_lt_of_isFastPlane (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (r₁ r₂ : ℝ) (h₁ : 0 ≤ r₁) (h₁₂ : r₁ < r₂)
    (hfin : dlambdaEnergy H {z | r₁ < ‖z‖} u ≠ ⊤) :
    dlambdaEnergy H {z | r₂ < ‖z‖} u < dlambdaEnergy H {z | r₁ < ‖z‖} u := by
  sorry

end FiniteEnergyPlane

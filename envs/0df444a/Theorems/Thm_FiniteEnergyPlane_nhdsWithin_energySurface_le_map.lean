-- Prove2me | Theorems.Thm_FiniteEnergyPlane_nhdsWithin_energySurface_le_map
-- name    : FiniteEnergyPlane.nhdsWithin_energySurface_le_map
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T12:36:40.099873+00:00
-- url     : https://prove2.me/theorems/4a67aa2d-06df-4283-91d1-ae04f30c7d4e
-- title:
--   Codimension-zero immersions into a star-shaped level are open
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level. Let $E$ be a real normed space of dimension $2n+1$ and $F$ a map into $\mathbb{R}^{2n+2}$ that is $C^1$ at $p\in E$, takes values in $S$ near $p$ and has injective derivative at $p$. Then $F$ maps every neighbourhood of $p$ to a neighbourhood of $F(p)$ in $S$.
--
--   Reusable for openness of evaluation maps of families of leaves.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- An immersion of codimension zero into `S` is open as a map to `S`. -/
theorem nhdsWithin_energySurface_le_map {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 2 * n + 1) (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (F : E → V n) (p : E) (hF : ContDiffAt ℝ 1 F p)
    (hFS : ∀ᶠ q in 𝓝 p, F q ∈ energySurface H) (hinj : Function.Injective (fderiv ℝ F p)) :
    𝓝[energySurface H] (F p) ≤ map F (𝓝 p) := by
  sorry

end FiniteEnergyPlane

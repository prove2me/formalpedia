-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_equiv_hasStrictFDerivAt_exp_smul_of_injective
-- name    : FiniteEnergyPlane.exists_equiv_hasStrictFDerivAt_exp_smul_of_injective
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-25T12:23:28.439715+00:00
-- url     : https://prove2.me/theorems/3cea702a-4128-4e0b-847b-fb4f1741c7ff
-- title:
--   The cone over an immersion into a star-shaped level
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level. Let $E$ be a real normed space of dimension $2n+1$ and $F$ a map into $\mathbb{R}^{2n+2}$ that is $C^1$ at $p\in E$, takes values in $S$ near $p$ and has injective derivative at $p$. Then $dH(F(p))\circ DF(p)=0$, and $(r,q)\mapsto e^rF(q)$ has the invertible strict derivative $(r,v)\mapsto rF(p)+DF(p)v$ at $(0,p)$.
--
--   Reusable for local coordinates of the symplectization near a point of $S$.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Section 7

import Definitions.Def_FiniteEnergyPlane_OpenBook

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The derivative of an immersion into `S` is tangent to `S`, and the cone over an immersion of codimension zero has an invertible strict derivative. -/
theorem exists_equiv_hasStrictFDerivAt_exp_smul_of_injective {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 2 * n + 1) (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (F : E → V n) (p : E) (hF : ContDiffAt ℝ 1 F p)
    (hFS : ∀ᶠ q in 𝓝 p, F q ∈ energySurface H) (hinj : Function.Injective (fderiv ℝ F p)) :
    (∀ v, fderiv ℝ H (F p) (fderiv ℝ F p v) = 0) ∧
    ∃ L : (ℝ × E) ≃L[ℝ] V n, (∀ q, L q = q.1 • F p + fderiv ℝ F p q.2) ∧
      HasStrictFDerivAt (fun q : ℝ × E => Real.exp q.1 • F q.2) (L : (ℝ × E) →L[ℝ] V n)
        ((0 : ℝ), p) := by
  sorry

end FiniteEnergyPlane

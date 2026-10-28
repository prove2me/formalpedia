-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendstoCInftyLocOn_comp
-- name    : FiniteEnergyPlane.tendstoCInftyLocOn_comp
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-25T22:05:22.355091+00:00
-- url     : https://prove2.me/theorems/91faa97f-2704-4fa5-8bc1-d7912de2bf2f
-- title:
--   C^∞_loc convergence is preserved under composition
-- statement:
--   Let $X,Y,Z$ be real normed spaces with $Y$ finite-dimensional, and let $U\subset X$ and $W\subset Y$ be open. Let $f_k,f:X\to Y$ be smooth on $U$ with $f_k(U)\subset W$ and $f(U)\subset W$, and let $g_k,g:Y\to Z$ be smooth on $W$. If $f_k\to f$ in $C^\infty_{\mathrm{loc}}(U)$ and $g_k\to g$ in $C^\infty_{\mathrm{loc}}(W)$, then $g_k\circ f_k\to g\circ f$ in $C^\infty_{\mathrm{loc}}(U)$.
--
--   **Formalization Note** $C^\infty_{\mathrm{loc}}$ convergence is `JHolomorphic.TendstoCInftyLocOn`: uniform convergence of every `iteratedFDeriv` on every compact subset of the given set.
-- source:
--   standard (e.g. C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, §2.4)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `C^∞_loc` convergence is preserved under composition. Let `U ⊆ X` and `W ⊆ Y` be open, with
`Y` finite-dimensional. Let `f_k, f : U → W` be smooth with `f_k → f` in `C^∞_loc(U)`, and let
`g_k, g` be smooth on `W` with `g_k → g` in `C^∞_loc(W)`. Then `g_k ∘ f_k → g ∘ f` in
`C^∞_loc(U)`. -/
theorem tendstoCInftyLocOn_comp {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {U : Set X} (hU : IsOpen U) {W : Set Y} (hW : IsOpen W)
    (f : ℕ → X → Y) (f₀ : X → Y) (g : ℕ → Y → Z) (g₀ : Y → Z)
    (hf : ∀ k, ContDiffOn ℝ ∞ (f k) U) (hf₀ : ContDiffOn ℝ ∞ f₀ U)
    (hg : ∀ k, ContDiffOn ℝ ∞ (g k) W) (hg₀ : ContDiffOn ℝ ∞ g₀ W)
    (hfW : ∀ k, Set.MapsTo (f k) U W) (hf₀W : Set.MapsTo f₀ U W)
    (hff : JHolomorphic.TendstoCInftyLocOn f f₀ U) (hgg : JHolomorphic.TendstoCInftyLocOn g g₀ W) :
    JHolomorphic.TendstoCInftyLocOn (fun k => g k ∘ f k) (g₀ ∘ f₀) U := by
  sorry

end FiniteEnergyPlane

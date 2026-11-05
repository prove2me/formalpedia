-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendstoCInftyLocOn_smul_of_tendsto
-- name    : FiniteEnergyPlane.tendstoCInftyLocOn_smul_of_tendsto
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T22:23:43.862562+00:00
-- url     : https://prove2.me/theorems/9e6cfdd5-478e-49c6-82c0-cd7ff80524a8
-- title:
--   $C^\infty_{\mathrm{loc}}$ convergence is preserved by convergent real scalars
-- statement:
--   Let $O$ be an open subset of a real normed space and let $f_k,g:O\to Y$ be smooth maps into a real normed space with $f_k\to g$ in $C^\infty_{\mathrm{loc}}(O)$. If $a_k\to a_0$ in $\mathbb{R}$, then $a_kf_k\to a_0g$ in $C^\infty_{\mathrm{loc}}(O)$.
--
--   Limits of radially rescaled curves in a symplectization are compared through this statement.
--
--   **Formalization Note** Convergence is `JHolomorphic.TendstoCInftyLocOn`: uniform convergence of `iteratedFDeriv ℝ m` on each compact subset of `O`, for every `m`.
-- source:
--   Auxiliary to U. Hryniewicz, Trans. AMS 364 (2012), arXiv:0812.4076, Section 4

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- If `fₖ → g` in `C^∞_loc(O)` on an open set `O`, all functions being smooth on `O`, and the real
numbers `aₖ` converge to `a₀`, then `aₖ • fₖ → a₀ • g` in `C^∞_loc(O)`. -/
theorem tendstoCInftyLocOn_smul_of_tendsto {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {f : ℕ → X → Y} {g : X → Y} {O : Set X}
    (hO : IsOpen O) (hf : ∀ k, ContDiffOn ℝ ∞ (f k) O) (hg : ContDiffOn ℝ ∞ g O)
    (hc : JHolomorphic.TendstoCInftyLocOn f g O) {a : ℕ → ℝ} {a₀ : ℝ}
    (ha : Tendsto a atTop (𝓝 a₀)) :
    JHolomorphic.TendstoCInftyLocOn (fun k z => a k • f k z) (fun z => a₀ • g z) O := by
  sorry

end FiniteEnergyPlane

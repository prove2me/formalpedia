-- Prove2me | Theorems.Thm_DSReg_uniform_pattern_margin
-- name    : DSReg.uniform_pattern_margin
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:32:02.13778+00:00
-- url     : https://prove2.me/theorems/a04ad2f8-3a55-4ee6-9e6c-8050d36750c4
-- title:
--   Lemma 6: uniform pattern margin
-- statement:
--   Let $x=g(z)$, with $g$ differentiable $\mu$-a.e. and measurable Jacobian $D$. Assume Structural Diversity and Functional no-cancellation with $d\ge2$. Let $\delta>0$ be such that $K_\delta=\{U\in O(d):\min_{P\in SP(d)}\|U-P\|_F\ge\delta\}$ is nonempty. Then the pattern margin is positive:
--
--   $$\rho^*(\delta)=\min_{U\in K_\delta}\rho^*(U)>0,$$
--
--   where $\rho^*(U)$ is the $(s^*{+}1)$-th largest of the values $v_{rj}(U)=\|U_{I_r,j}\|_2$ and $s^*=\sum_i|\mathcal S_i|$.
--
--   **Formalization Note** $\rho^*(\delta)$ is the infimum over $K_\delta$, taken in the extended reals.
-- source:
--   Zheng, Klindt, Balestriero and Schölkopf, DSReg: Provably Recovering Individual World Latents without Reconstruction, arXiv:2610.09457v1 (2026), Appendix A.4, Lemma 6, p. 22

import Mathlib
import Definitions.Def_DSReg_Basic

open MeasureTheory

namespace DSReg

theorem uniform_pattern_margin {d p : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (g : (Fin d → ℝ) → Fin p → ℝ) (hdiff : ∀ᵐ z ∂μ, DifferentiableAt ℝ g z)
    (hmeas : ∀ r i, Measurable fun z => depJac g z r i)
    (hsd : StructuralDiversity (footprint μ (depJac g)))
    (hfnc : FunctionalNoCancellation μ (depJac g)) (hd : 2 ≤ d)
    (δ : ℝ) (hδ : 0 < δ) (hK : ∃ U ∈ Matrix.orthogonalGroup (Fin d) ℝ, δ ≤ distSP U) :
    0 < rhoStar μ (depJac g) δ := by sorry

end DSReg

-- Prove2me | Theorems.Thm_Arxivcond_mat_0004049_coherent_backscattering_peak_enhancement
-- name    : Arxivcond_mat_0004049.coherent_backscattering_peak_enhancement
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T20:14:36.02562+00:00
-- url     : https://prove2.me/theorems/a32da245-cd02-5c71-8b21-09a0b45895db
-- title:
--   Coherent backscattering enhancement of the delay-time peak
-- statement:
--   Let $\gamma>0$. In the localized-regime model, the laws of the single-mode delay time $\varphi'/(\gamma N^{3/2})$ converge as $N\to\infty$, both for $n\ne m$ ($\varphi'=\mathrm{Re}\,A_1/A_0$) and for $n=m$ ($\varphi'=\mathrm{Re}\,C_1/C_0$), to laws with continuous bounded densities $g_{\ne}$ and $g_=$. Their maxima satisfy
--
--   $$\sup g_= =\sqrt{2/\pi},\qquad \sup g_= =\sqrt2\times\frac{4096}{1371\pi}\,\sup g_{\ne}.$$
--
--   So for $n=m$ the peak value of $P(\varphi')$ is $P(\varphi'_{\rm peak})=\sqrt{2/(\pi N^3\gamma^2)}$ in the large-$N$ limit, larger than the peak value for $n\ne m$ by the factor $\sqrt2\times4096/(1371\pi)\approx1.345$.
--
--   **Formalization Note** "The maximal value of $P(\varphi')$ in the large-$N$ limit" is the maximum of the limiting density on the scale $\gamma N^{3/2}$ of the peak width, so $P(\varphi'_{\rm peak})=\sup g/(\gamma N^{3/2})$. The paper prints the factor as $1.35$; the closed form is $1.3449$.
-- source:
--   Schomerus, van Bemmel and Beenakker, Coherent backscattering effect on wave dynamics in a random medium, arXiv:cond-mat/0004049v1 (2000), claim c017; text after eq. (20), PDF p. 3

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

theorem coherent_backscattering_peak_enhancement (γ : ℝ) (hγ : 0 < γ) :
    ∃ gNe gEq : ℝ → ℝ, Continuous gNe ∧ Continuous gEq ∧ (∀ y, 0 ≤ gNe y) ∧ (∀ y, 0 ≤ gEq y) ∧
      LawTendsto γ
        (fun N (ω : Sample N) => delayNe ω / (γ * N * Real.sqrt N))
        ((volume : Measure ℝ).withDensity (fun y => ENNReal.ofReal (gNe y))) ∧
      LawTendsto γ
        (fun N (ω : Sample N) => delayEq ω / (γ * N * Real.sqrt N))
        ((volume : Measure ℝ).withDensity (fun y => ENNReal.ofReal (gEq y))) ∧
      BddAbove (Set.range gNe) ∧ BddAbove (Set.range gEq) ∧
      (⨆ y, gEq y) = Real.sqrt (2 / Real.pi) ∧
      (⨆ y, gEq y) = Real.sqrt 2 * (4096 / (1371 * Real.pi)) * ⨆ y, gNe y := by sorry

end Arxivcond_mat_0004049

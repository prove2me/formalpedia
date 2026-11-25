-- Prove2me | Theorems.Thm_Arxiv2608_05214_true_amplitude_least_squares
-- name    : Arxiv2608_05214.true_amplitude_least_squares
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:17:48.938809+00:00
-- url     : https://prove2.me/theorems/c3f97655-0ed8-5f77-8354-68fcf233d293
-- title:
--   Eq. (58): the illumination-compensated image is the least-squares scalar reflectivity
-- statement:
--   Let $(S,\mu)$ be the acquisition surface $\partial\mathbb D_0$ with a $\sigma$-finite measure. Let $G^+,G^-:S\times\mathbb R\to\mathbb R$ be the real downgoing and upgoing Green's functions at a fixed focal point $x_A$, both square integrable, with positive illumination $\iint (G^+)^2\,dt\,d\mu>0$. Let
--
--   $$I_{\mathrm{TA}}(x_A)=\frac{\displaystyle\int_{\partial\mathbb D_0}\int G^+G^-\,dt\,dx_H}{\displaystyle\int_{\partial\mathbb D_0}\int |G^+|^2\,dt\,dx_H}.$$
--
--   Then $I_{\mathrm{TA}}$ is the least-squares estimate of a scalar reflectivity at $x_A$: it minimises $r\mapsto\iint|G^--rG^+|^2\,dt\,dx_H$ over $r\in\mathbb R$, and it is the only minimiser.
--
--   **Formalization Note** The paper does not write out the least-squares objective. The misfit $\iint|G^--rG^+|^2$ is the reading under which eq. (58) is the least-squares estimate.
-- source:
--   H. A. Oyekan, Marchenko Theory, Algorithms, and Applications: A Review, arXiv:2608.05214v1 (2026), claim c022; Section VIII-B (True-Amplitude Marchenko Imaging), eq. (58), PDF p. 15

import Mathlib
import Definitions.Def_Arxiv2608_05214_Basic

open MeasureTheory Filter Topology
open scoped ContDiff

namespace Arxiv2608_05214

theorem true_amplitude_least_squares {S : Type*} [MeasurableSpace S] (μ : Measure S)
    [SigmaFinite μ] (Gp Gm : S → ℝ → ℝ)
    (hGp : MemLp (fun p : S × ℝ => Gp p.1 p.2) 2 (μ.prod volume))
    (hGm : MemLp (fun p : S × ℝ => Gm p.1 p.2) 2 (μ.prod volume))
    (hillum : 0 < ∫ p, Gp p.1 p.2 ^ 2 ∂(μ.prod volume)) :
    (∀ r : ℝ, scalarReflectivityMisfit μ Gp Gm (trueAmplitudeImage μ Gp Gm) ≤
        scalarReflectivityMisfit μ Gp Gm r) ∧
    (∀ r : ℝ, scalarReflectivityMisfit μ Gp Gm r =
        scalarReflectivityMisfit μ Gp Gm (trueAmplitudeImage μ Gp Gm) →
      r = trueAmplitudeImage μ Gp Gm) := by sorry

end Arxiv2608_05214

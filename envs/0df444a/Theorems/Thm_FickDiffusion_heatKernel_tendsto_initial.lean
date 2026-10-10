-- Prove2me | Theorems.Thm_FickDiffusion_heatKernel_tendsto_initial
-- name    : FickDiffusion.heatKernel_tendsto_initial
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:57.71665+00:00
-- url     : https://prove2.me/theorems/728aeb7a-f5fd-4f29-8084-66076554df09
-- title:
--   The 1D diffusion kernel converges to a Dirac mass as t → 0⁺
-- statement:
--   Let $D>0$, let $f:\mathbb R\to\mathbb R$ be continuous and bounded, and let $x\in\mathbb R$. Then
--   $$\lim_{t\to0^+}\int_{-\infty}^{\infty}\frac{1}{\sqrt{4\pi Dt}}\exp\Big(-\frac{(x-y)^2}{4Dt}\Big)f(y)\,dy=f(x).$$
--
--   Equivalently, $\varphi_D(\cdot,t)\to\delta_0$ in the sense of distributions tested against bounded continuous functions: the diffusion kernel is the solution of Fick's second law started from a unit point source.
--
--   **Formalization Note** The limit is taken along $t\to0$ with $t>0$ (`𝓝[>] 0`). Boundedness is stated as the existence of $C$ with $|f(y)|\le C$ for all $y$.
-- source:
--   Wikipedia, "Fick's laws of diffusion" (PDF snapshot supplied by the proposer, 21 pp.), https://en.wikipedia.org/wiki/Fick%27s_laws_of_diffusion, section "Fick's second law" (p. 4): φ is the fundamental solution (heat kernel)

import Mathlib
import Definitions.Def_FickDiffusion_defs

open Real Filter Topology MeasureTheory

namespace FickDiffusion

theorem heatKernel_tendsto_initial (D : ℝ) (hD : 0 < D) (f : ℝ → ℝ) (hf : Continuous f)
    (hbdd : ∃ C, ∀ y, |f y| ≤ C) (x : ℝ) :
    Tendsto (fun t => ∫ y, heatKernel D (x - y) t * f y) (𝓝[>] 0) (𝓝 (f x)) := by sorry

end FickDiffusion

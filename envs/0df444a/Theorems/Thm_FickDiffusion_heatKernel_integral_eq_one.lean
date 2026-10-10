-- Prove2me | Theorems.Thm_FickDiffusion_heatKernel_integral_eq_one
-- name    : FickDiffusion.heatKernel_integral_eq_one
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:30.168166+00:00
-- url     : https://prove2.me/theorems/6831cdd1-2331-4518-970d-9a7d8d9883c5
-- title:
--   The 1D diffusion kernel has unit mass
-- statement:
--   Let $D>0$ and $t>0$. Then
--   $$\int_{-\infty}^{\infty}\frac{1}{\sqrt{4\pi Dt}}\exp\Big(-\frac{x^2}{4Dt}\Big)\,dx=1 .$$
--
--   The total amount of diffusing substance carried by the fundamental solution is one unit at every positive time; this is the normalization implicit in calling $\varphi_D$ the fundamental solution.
--
--   **Formalization Note** The integral is the Lebesgue integral over $\mathbb R$; the integrand is integrable, so no junk value arises.
-- source:
--   Wikipedia, "Fick's laws of diffusion" (PDF snapshot supplied by the proposer, 21 pp.), https://en.wikipedia.org/wiki/Fick%27s_laws_of_diffusion, section "Fick's second law" (p. 4), the fundamental solution φ(x,t)=(4πDt)^{-1/2} exp(-x²/(4Dt))

import Mathlib
import Definitions.Def_FickDiffusion_defs

open Real Filter Topology MeasureTheory

namespace FickDiffusion

theorem heatKernel_integral_eq_one (D : ℝ) (hD : 0 < D) (t : ℝ) (ht : 0 < t) :
    ∫ x, heatKernel D x t = 1 := by sorry

end FickDiffusion

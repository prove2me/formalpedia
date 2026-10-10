-- Prove2me | Theorems.Thm_FickDiffusion_heatKernel_fick_second_law
-- name    : FickDiffusion.heatKernel_fick_second_law
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:52.618206+00:00
-- url     : https://prove2.me/theorems/fa188317-9fe0-4b3f-85a9-85f8a50bc597
-- title:
--   The 1D diffusion kernel satisfies Fick's second law
-- statement:
--   Let $D>0$ and let
--   $$\varphi_D(x,t)=\frac{1}{\sqrt{4\pi Dt}}\exp\Big(-\frac{x^2}{4Dt}\Big).$$
--   Then for every $x\in\mathbb R$ and every $t>0$,
--   $$\frac{\partial\varphi_D}{\partial t}(x,t)=D\,\frac{\partial^2\varphi_D}{\partial x^2}(x,t).$$
--
--   This is the statement that the Gaussian kernel is a classical solution of Fick's second law (the one-dimensional diffusion equation) for positive times.
--
--   **Formalization Note** Both sides are written with Mathlib's one-variable `deriv`; the kernel is smooth on $\{t>0\}$, so these are the genuine partial derivatives.
-- source:
--   Wikipedia, "Fick's laws of diffusion" (PDF snapshot supplied by the proposer, 21 pp.), https://en.wikipedia.org/wiki/Fick%27s_laws_of_diffusion, section "Fick's second law" (p. 4), last displayed equation, and the one-dimensional equation at the top of the section

import Mathlib
import Definitions.Def_FickDiffusion_defs

open Real Filter Topology MeasureTheory

namespace FickDiffusion

theorem heatKernel_fick_second_law (D : ℝ) (hD : 0 < D) (x t : ℝ) (ht : 0 < t) :
    deriv (fun s => heatKernel D x s) t =
      D * deriv (fun y => deriv (fun z => heatKernel D z t) y) x := by sorry

end FickDiffusion

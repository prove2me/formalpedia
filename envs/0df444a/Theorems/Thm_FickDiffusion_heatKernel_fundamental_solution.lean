-- Prove2me | Theorems.Thm_FickDiffusion_heatKernel_fundamental_solution
-- name    : FickDiffusion.heatKernel_fundamental_solution
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:49.425731+00:00
-- url     : https://prove2.me/theorems/4d8c5125-6d88-4cea-ad17-2a9047e70f30
-- title:
--   Fick's second law: φ(x,t) = (4πDt)^{-1/2} exp(-x²/(4Dt)) is its fundamental solution
-- statement:
--   Let $D>0$ be a diffusion coefficient and let
--   $$\varphi_D(x,t)=\frac{1}{\sqrt{4\pi Dt}}\exp\Big(-\frac{x^2}{4Dt}\Big)\qquad(x\in\mathbb R,\ t>0).$$
--   Then $\varphi_D$ is the fundamental solution of Fick's second law $\partial_t\varphi=D\,\partial_x^2\varphi$:
--
--   1. **it solves the equation:** for all $x\in\mathbb R$ and $t>0$,
--   $$\frac{\partial\varphi_D}{\partial t}(x,t)=D\,\frac{\partial^2\varphi_D}{\partial x^2}(x,t);$$
--   2. **it carries unit mass:** for every $t>0$, $\displaystyle\int_{-\infty}^{\infty}\varphi_D(x,t)\,dx=1$;
--   3. **it starts from a unit point source:** for every bounded continuous $f:\mathbb R\to\mathbb R$ and every $x\in\mathbb R$,
--   $$\lim_{t\to0^+}\int_{-\infty}^{\infty}\varphi_D(x-y,t)\,f(y)\,dy=f(x).$$
--
--   This is the article's identification of the fundamental solution of Fick's second law with the heat kernel (thermal diffusivity replaced by $D$); every solution of the 1D diffusion equation with bounded continuous initial data is obtained by convolving that data with $\varphi_D$.
--
--   **Formalization Note** Derivatives are Mathlib's one-variable `deriv`; the limit in clause 3 is the right-sided limit `𝓝[>] 0`; boundedness of $f$ is the existence of $C$ with $|f(y)|\le C$.
-- source:
--   Wikipedia, "Fick's laws of diffusion" (PDF snapshot supplied by the proposer, 21 pp.), https://en.wikipedia.org/wiki/Fick%27s_laws_of_diffusion, section "Fick's second law" (p. 4): "Fick's second law has the same mathematical form as the Heat equation and its fundamental solution is the same as the Heat kernel, except switching thermal conductivity k with diffusion coefficient D"

import Mathlib
import Definitions.Def_FickDiffusion_defs

open Real Filter Topology MeasureTheory

namespace FickDiffusion

theorem heatKernel_fundamental_solution (D : ℝ) (hD : 0 < D) :
    (∀ x t : ℝ, 0 < t → deriv (fun s => heatKernel D x s) t =
        D * deriv (fun y => deriv (fun z => heatKernel D z t) y) x) ∧
    (∀ t : ℝ, 0 < t → ∫ x, heatKernel D x t = 1) ∧
    (∀ f : ℝ → ℝ, Continuous f → (∃ C, ∀ y, |f y| ≤ C) → ∀ x : ℝ,
        Tendsto (fun t => ∫ y, heatKernel D (x - y) t * f y) (𝓝[>] 0) (𝓝 (f x))) := by sorry

end FickDiffusion

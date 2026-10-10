-- Prove2me | Theorems.Thm_FickDiffusion_mean_squared_displacement
-- name    : FickDiffusion.mean_squared_displacement
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:33:21.060734+00:00
-- url     : https://prove2.me/theorems/0fe3e080-a8df-481c-a2b6-56944fbefbe4
-- title:
--   Example solution 2: mean squared displacement ⟨‖x‖²⟩ = 2nDt
-- statement:
--   Let $n\in\mathbb N$, $D>0$ and $t>0$. The position (relative to its starting point) of a particle diffusing in $\mathbb R^n$ with diffusion coefficient $D$ has density $\varphi^{(n)}_D(\cdot,t)$ at time $t$, where
--   $$\varphi^{(n)}_D(x,t)=(4\pi Dt)^{-n/2}\exp\Big(-\frac{\|x\|^2}{4Dt}\Big).$$
--   Its mean squared displacement is
--   $$\int_{\mathbb R^n}\|x\|^2\,\varphi^{(n)}_D(x,t)\,dx=2nDt .$$
--
--   This is the diffusion-length law used throughout the article: the root-mean-square distance travelled grows like $\sqrt{2nDt}$.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` with its Lebesgue (volume) measure and Euclidean norm; the Brownian particle is modelled by its Gaussian transition density, i.e. the $n$-dimensional fundamental solution of Fick's second law. For $n=0$ both sides are $0$.
-- source:
--   Wikipedia, "Fick's laws of diffusion" (PDF snapshot supplied by the proposer, 21 pp.), https://en.wikipedia.org/wiki/Fick%27s_laws_of_diffusion, section "Example solution 2: Brownian particle and mean squared displacement" (p. 7), first displayed equation

import Mathlib
import Definitions.Def_FickDiffusion_defs

open Real Filter Topology MeasureTheory

namespace FickDiffusion

theorem mean_squared_displacement (n : ℕ) (D t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    ∫ x, ‖x‖ ^ 2 * heatKernelEuclid n D x t = 2 * n * D * t := by sorry

end FickDiffusion

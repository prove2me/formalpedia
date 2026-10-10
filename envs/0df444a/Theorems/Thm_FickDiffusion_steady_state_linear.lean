-- Prove2me | Theorems.Thm_FickDiffusion_steady_state_linear
-- name    : FickDiffusion.steady_state_linear
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:31.905236+00:00
-- url     : https://prove2.me/theorems/249df9b2-c954-4414-814c-f9bef25ff7d2
-- title:
--   Steady state of Fick's second law in one dimension is linear
-- statement:
--   Let $D>0$ be a constant diffusion coefficient and let $c:\mathbb R\to\mathbb R$ be a twice continuously differentiable, time-independent concentration profile. If $c$ is a steady state of Fick's second law, i.e.
--   $$D\,c''(x)=0\quad\text{for all }x\in\mathbb R,$$
--   then $c$ is linear (affine): there are constants $a,b\in\mathbb R$ with
--   $$c(x)=a x+b\qquad\text{for all }x\in\mathbb R.$$
--
--   **Formalization Note** A steady state is modelled as a function of $x$ alone (so $\partial_t\varphi=0$). The hypothesis that $c$ is $C^2$ is the field's standing smoothness convention; without it Lean's `deriv` (which is $0$ at non-differentiable points) would let non-smooth functions such as $|x|$ satisfy the equation. $D>0$ is the physical sign of a diffusion coefficient.
-- source:
--   Wikipedia, "Fick's laws of diffusion" (PDF snapshot supplied by the proposer, 21 pp.), https://en.wikipedia.org/wiki/Fick%27s_laws_of_diffusion, section "Derivation of Fick's second law" (p. 5), paragraph beginning "An important example is the case where φ is at a steady state"

import Mathlib
import Definitions.Def_FickDiffusion_defs

open Real Filter Topology MeasureTheory

namespace FickDiffusion

theorem steady_state_linear (D : ℝ) (hD : 0 < D) (c : ℝ → ℝ) (hc : ContDiff ℝ 2 c)
    (hsteady : ∀ x, D * deriv (deriv c) x = 0) :
    ∃ a b : ℝ, ∀ x, c x = a * x + b := by sorry

end FickDiffusion

-- Prove2me | Theorems.Thm_FiniteEnergyPlane_ds_dt_comp_of_hasDerivAt
-- name    : FiniteEnergyPlane.ds_dt_comp_of_hasDerivAt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T10:21:29.647203+00:00
-- url     : https://prove2.me/theorems/ac3a9023-ffb9-4833-9227-4903337547ee
-- title:
--   Partial derivatives under a holomorphic change of variables
-- statement:
--   Let $F$ be a real normed space, $g:\mathbb{C}\to F$ real differentiable at $f(z)$, and $f:\mathbb{C}\to\mathbb{C}$ complex differentiable at $z$ with $f'(z)=c$. Writing $\partial_s$, $\partial_t$ for the derivatives in the directions $1$ and $i$, $$\partial_s(g\circ f)(z)=(\operatorname{Re}c)\,\partial_sg(f(z))+(\operatorname{Im}c)\,\partial_tg(f(z)),\qquad \partial_t(g\circ f)(z)=-(\operatorname{Im}c)\,\partial_sg(f(z))+(\operatorname{Re}c)\,\partial_tg(f(z)).$$
--
--   This expresses how the pair $(\partial_s,\partial_t)$ transforms under conformal reparametrizations of the domain; it is used to transport energy densities.
--
--   **Formalization Note** $\partial_s g(z)$ and $\partial_t g(z)$ are `ds g z = fderiv ℝ g z 1` and `dt g z = fderiv ℝ g z Complex.I`.
-- source:
--   Used for U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.11 (case of planes)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Partial derivatives `∂ₛ`, `∂ₜ` of `g ∘ f` for a complex-differentiable change of variables
`f` with `f'(z) = c`: `∂ₛ(g ∘ f)(z) = (Re c) ∂ₛg(f z) + (Im c) ∂ₜg(f z)` and
`∂ₜ(g ∘ f)(z) = -(Im c) ∂ₛg(f z) + (Re c) ∂ₜg(f z)`. -/
theorem ds_dt_comp_of_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℂ → F) (f : ℂ → ℂ) (z c : ℂ) (hf : HasDerivAt f c z)
    (hg : DifferentiableAt ℝ g (f z)) :
    ds (fun w => g (f w)) z = c.re • ds g (f z) + c.im • dt g (f z) ∧
      dt (fun w => g (f w)) z = -c.im • ds g (f z) + c.re • dt g (f z) := by
  sorry

end FiniteEnergyPlane

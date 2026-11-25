-- Prove2me | Theorems.Thm_Arxiv1110_5134_gvrte_eulerian_ray
-- name    : Arxiv1110_5134.gvrte_eulerian_ray
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T09:17:16.925865+00:00
-- url     : https://prove2.me/theorems/bafec5ee-759c-4183-8fc2-e54f5eb97f13
-- title:
--   Eqs. (40)-(41): Eulerian form of the GVRTE in the ray coordinate
-- statement:
--   Let $\mathbf I(t,s)$ be a time-dependent Stokes field along a ray, jointly differentiable in $(t,s)$ at the point $(\tau(s),s)$. Let $n(s)>0$ be differentiable, let $c>0$, and let the beam reach the point $s$ at time $t=\tau(s)$ with $d\tau/ds=n/c$. Then (Eq. 40)
--
--   $$n^2\frac{d}{ds}\Big[\frac{\mathbf I(\tau(s),s)}{n^2}\Big]=\frac nc\frac{\partial\mathbf I}{\partial t}+n^2\frac{\partial}{\partial s}\Big[\frac{\mathbf I}{n^2}\Big].$$
--
--   Consequently, the GVRTE (Eq. 20) along the ray is equivalent to its Eulerian form in the ray coordinate (Eq. 41):
--
--   $$\frac nc\frac{\partial\mathbf I}{\partial t}+n^2\frac{\partial}{\partial s}\Big[\frac{\mathbf I}{n^2}\Big]+(\boldsymbol\kappa_e+\mathbf R)\mathbf I=\boldsymbol\kappa_a\mathbf I_b+\frac1{4\pi}\int_{4\pi}\mathbf Z(\boldsymbol\Omega',\boldsymbol\Omega)\mathbf I(t,s,\boldsymbol\Omega')\,d\Omega'.$$
--
--   **Formalization Note** The statement is at one point $s$ with $t=\tau(s)$. The incident field in the integral is an arbitrary function of direction.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c014; Section 4.2.1, Eqs. (40)-(41), PDF p. 18

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem gvrte_eulerian_ray (n : ℝ → ℝ) (c : ℝ) (hc : 0 < c) (F : ℝ → ℝ → Stokes)
    (τ : ℝ → ℝ) (s : ℝ) (hn : 0 < n s) (hnd : DifferentiableAt ℝ n s)
    (hτ : HasDerivAt τ (n s / c) s)
    (hF : DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (τ s, s))
    (κe κa : Matrix (Fin 4) (Fin 4) ℝ) (κ : ℝ) (Ib : Stokes)
    (Z : Dir → Matrix (Fin 4) (Fin 4) ℝ) (L : Dir → Stokes) :
    transportOp n (fun t => F (τ t) t) s =
      (n s / c) • deriv (fun t' => F t' s) (τ s) + transportOp n (F (τ s)) s ∧
    (transportOp n (fun t => F (τ t) t) s + (κe + rytovMatrix κ) *ᵥ F (τ s) s =
        κa *ᵥ Ib + scatSource Z L ↔
      (n s / c) • deriv (fun t' => F t' s) (τ s) + transportOp n (F (τ s)) s +
          (κe + rytovMatrix κ) *ᵥ F (τ s) s = κa *ᵥ Ib + scatSource Z L) := by sorry

end Arxiv1110_5134

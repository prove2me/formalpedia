-- Prove2me | Theorems.Thm_Arxiv1110_5134_trad_cylindrical_streaming_forms
-- name    : Arxiv1110_5134.trad_cylindrical_streaming_forms
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T09:19:03.474801+00:00
-- url     : https://prove2.me/theorems/dd659d87-4d6c-48b1-b8a5-097b402f207a
-- title:
--   Eqs. (50)-(51): streaming term in traditional cylindrical coordinates (as corrected)
-- statement:
--   In the traditional cylindrical coordinates $(\rho,\Psi,z)$ of Fig. 7(a), let $\partial/\partial s$ be the streaming operator of Eq. (49):
--
--   $$\frac{\partial}{\partial s}=\boldsymbol\Omega\cdot\nabla-\frac\eta\rho\frac{\partial}{\partial\varphi}+\frac1{\sin\theta}\Big\{\Big[(\xi\boldsymbol\Omega-\mathbf e_z)\cdot\frac{\nabla n}n\Big]\frac{\partial}{\partial\theta}+\Big[\mathbf s_1\cdot\frac{\nabla n}n\Big]\frac{\partial}{\partial\varphi}\Big\}.$$
--
--   Here $\boldsymbol\Omega=\mu\mathbf e_\rho+\eta\mathbf e_\Psi+\xi\mathbf e_z$ and $\nabla=\mathbf e_\rho\partial_\rho+\mathbf e_\Psi\rho^{-1}\partial_\Psi+\mathbf e_z\partial_z$. Assume $\rho>0$, $n>0$, $\sin\theta\ne0$, and differentiability of $n$ and $\mathbf I$ at the point. Then the non-conservative form (Eq. 50) holds,
--
--   $$n^2\frac{\partial}{\partial s}\Big[\frac{\mathbf I}{n^2}\Big]=\boldsymbol\Omega\cdot\nabla\mathbf I-\frac\eta\rho\frac{\partial\mathbf I}{\partial\varphi}+\frac1{\sin\theta}\Big\{\Big[(\xi\boldsymbol\Omega-\mathbf e_z)\cdot\frac{\nabla n}n\Big]\frac{\partial\mathbf I}{\partial\theta}+\Big[\mathbf s_1\cdot\frac{\nabla n}n\Big]\frac{\partial\mathbf I}{\partial\varphi}\Big\}-2\Big(\boldsymbol\Omega\cdot\frac{\nabla n}n\Big)\mathbf I,$$
--
--   and so does the conservative form (Eq. 51)
--
--   $$n^2\frac{\partial}{\partial s}\Big[\frac{\mathbf I}{n^2}\Big]=\boldsymbol\Omega\cdot\tilde\nabla\mathbf I-\frac1\rho\frac{\partial(\eta\mathbf I)}{\partial\varphi}+\frac1{\sin\theta}\Big\{\frac{\partial}{\partial\theta}\Big[\Big((\xi\boldsymbol\Omega-\mathbf e_z)\cdot\frac{\nabla n}n\Big)\mathbf I\Big]+\frac{\partial}{\partial\varphi}\Big[\Big(\mathbf s_1\cdot\frac{\nabla n}n\Big)\mathbf I\Big]\Big\},$$
--
--   with the modified gradient $\tilde\nabla(\cdot)=\mathbf e_\rho\rho^{-1}\partial(\rho\,\cdot)/\partial\rho+\mathbf e_\Psi\rho^{-1}\partial(\cdot)/\partial\Psi+\mathbf e_z\partial(\cdot)/\partial z$.
--
--   **Formalization Note** As printed, the modified gradient of Eq. (51) has $\mathbf e_z\rho^{-1}\partial/\partial z$. With that factor the conservative form differs from Eq. (50) by $\xi(\rho^{-1}-1)\partial_z\mathbf I$, so the statement uses $\mathbf e_z\partial/\partial z$ (as corrected). Eq. (49) is quoted from Ref. [29] and is taken as the definition of $\partial/\partial s$.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c028; Section 4.2.2, Eqs. (49)-(51), PDF p. 21

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem trad_cylindrical_streaming_forms (n : Vec3 → ℝ) (F : Vec3 → ℝ → ℝ → Stokes)
    (q : Vec3) (θ φ : ℝ) (hρ : 0 < q 0) (hn : 0 < n q) (hnd : DifferentiableAt ℝ n q)
    (hFq : DifferentiableAt ℝ (fun y => F y θ φ) q)
    (hFθ : DifferentiableAt ℝ (fun θ' => F q θ' φ) θ)
    (hFφ : DifferentiableAt ℝ (fun φ' => F q θ φ') φ) (hθ : Real.sin θ ≠ 0) :
    n q ^ 2 • tradCylStream n (fun y θ' φ' => (n y ^ 2)⁻¹ • F y θ' φ') q θ φ =
      dirDot θ φ (tradCylGrad (fun y => F y θ φ) q) -
        (Real.sin θ * Real.sin φ / q 0) • dPhi F q θ φ +
        angularStream ((n q)⁻¹ • tradCylGrad n q) F q θ φ -
        (2 * (dirVec θ φ ⬝ᵥ ((n q)⁻¹ • tradCylGrad n q))) • F q θ φ ∧
    n q ^ 2 • tradCylStream n (fun y θ' φ' => (n y ^ 2)⁻¹ • F y θ' φ') q θ φ =
      (Real.sin θ * Real.cos φ) • ((q 0)⁻¹ • pd (fun y => y 0 • F y θ φ) 0 q) +
        (Real.sin θ * Real.sin φ) • ((q 0)⁻¹ • pd (fun y => F y θ φ) 1 q) +
        Real.cos θ • pd (fun y => F y θ φ) 2 q -
        (q 0)⁻¹ • deriv (fun φ' => (Real.sin θ * Real.sin φ') • F q θ φ') φ +
        angularCons ((n q)⁻¹ • tradCylGrad n q) F q θ φ := by sorry

end Arxiv1110_5134

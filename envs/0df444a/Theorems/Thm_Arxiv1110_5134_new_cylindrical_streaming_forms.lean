-- Prove2me | Theorems.Thm_Arxiv1110_5134_new_cylindrical_streaming_forms
-- name    : Arxiv1110_5134.new_cylindrical_streaming_forms
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T09:19:24.706939+00:00
-- url     : https://prove2.me/theorems/c41977c0-3f88-4ad4-b94b-e6b5a99c934e
-- title:
--   Eqs. (53)-(54): streaming term in the new cylindrical coordinates (as corrected)
-- statement:
--   In the new cylindrical coordinates $(\rho,\Psi,z)$ of Fig. 7(b), with $\boldsymbol\Omega=\mu\mathbf e_\Psi+\eta\mathbf e_z+\xi\mathbf e_\rho$, $\mathbf s_1=-\sin\varphi\,\mathbf e_\Psi+\cos\varphi\,\mathbf e_z$ and $\nabla=\mathbf e_\Psi\rho^{-1}\partial_\Psi+\mathbf e_z\partial_z+\mathbf e_\rho\partial_\rho$, let $\partial/\partial s$ be the streaming operator of Eq. (52):
--
--   $$\frac{\partial}{\partial s}=\boldsymbol\Omega\cdot\nabla-\mu\frac{\cos\varphi}\rho\frac{\partial}{\partial\theta}+\xi\frac{\sin\varphi\cos\varphi}\rho\frac{\partial}{\partial\varphi}+\frac1{\sin\theta}\Big\{\Big[(\xi\boldsymbol\Omega-\mathbf e_\rho)\cdot\frac{\nabla n}n\Big]\frac{\partial}{\partial\theta}+\Big[\mathbf s_1\cdot\frac{\nabla n}n\Big]\frac{\partial}{\partial\varphi}\Big\}.$$
--
--   Assume $\rho>0$, $n>0$, $\sin\theta\ne0$, and differentiability of $n$ and $\mathbf I$ at the point. Then the non-conservative form (Eq. 53) holds,
--
--   $$n^2\frac{\partial}{\partial s}\Big[\frac{\mathbf I}{n^2}\Big]=\boldsymbol\Omega\cdot\nabla\mathbf I-\mu\frac{\cos\varphi}\rho\frac{\partial\mathbf I}{\partial\theta}+\xi\frac{\sin\varphi\cos\varphi}\rho\frac{\partial\mathbf I}{\partial\varphi}+\frac1{\sin\theta}\Big\{\Big[(\xi\boldsymbol\Omega-\mathbf e_\rho)\cdot\frac{\nabla n}n\Big]\frac{\partial\mathbf I}{\partial\theta}+\Big[\mathbf s_1\cdot\frac{\nabla n}n\Big]\frac{\partial\mathbf I}{\partial\varphi}\Big\}-2\Big(\boldsymbol\Omega\cdot\frac{\nabla n}n\Big)\mathbf I,$$
--
--   and so does the conservative form (Eq. 54)
--
--   $$n^2\frac{\partial}{\partial s}\Big[\frac{\mathbf I}{n^2}\Big]=\boldsymbol\Omega\cdot\tilde\nabla\mathbf I-\frac1{\rho\sin\theta}\frac{\partial}{\partial\theta}[\mu^2\mathbf I]+\frac1\rho\frac{\partial}{\partial\varphi}[\xi\sin\varphi\cos\varphi\,\mathbf I]+\frac1{\sin\theta}\Big\{\frac{\partial}{\partial\theta}\Big[\Big((\xi\boldsymbol\Omega-\mathbf e_\rho)\cdot\frac{\nabla n}n\Big)\mathbf I\Big]+\frac{\partial}{\partial\varphi}\Big[\Big(\mathbf s_1\cdot\frac{\nabla n}n\Big)\mathbf I\Big]\Big\},$$
--
--   with $\tilde\nabla(\cdot)=\mathbf e_\Psi\rho^{-1}\partial(\cdot)/\partial\Psi+\mathbf e_z\partial(\cdot)/\partial z+\mathbf e_\rho\rho^{-1}\partial(\rho\,\cdot)/\partial\rho$.
--
--   **Formalization Note** As printed, Eq. (54) has $\xi\boldsymbol\Omega-\mathbf e_z$ in its $\theta$-flux. Eqs. (52)-(53) have $\xi\boldsymbol\Omega-\mathbf e_\rho$, and only that choice makes Eq. (54) agree with Eq. (53), so the statement uses $\mathbf e_\rho$ (as corrected). Eq. (52) is quoted from Ref. [30] and is taken as the definition of $\partial/\partial s$.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c029; Section 4.2.2, Eqs. (52)-(54), PDF p. 22

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem new_cylindrical_streaming_forms (n : Vec3 → ℝ) (F : Vec3 → ℝ → ℝ → Stokes)
    (q : Vec3) (θ φ : ℝ) (hρ : 0 < q 0) (hn : 0 < n q) (hnd : DifferentiableAt ℝ n q)
    (hFq : DifferentiableAt ℝ (fun y => F y θ φ) q)
    (hFθ : DifferentiableAt ℝ (fun θ' => F q θ' φ) θ)
    (hFφ : DifferentiableAt ℝ (fun φ' => F q θ φ') φ) (hθ : Real.sin θ ≠ 0) :
    n q ^ 2 • newCylStream n (fun y θ' φ' => (n y ^ 2)⁻¹ • F y θ' φ') q θ φ =
      dirDot θ φ (newCylGrad (fun y => F y θ φ) q) -
        (Real.sin θ * Real.cos φ * Real.cos φ / q 0) • dTheta F q θ φ +
        (Real.cos θ * Real.sin φ * Real.cos φ / q 0) • dPhi F q θ φ +
        angularStream ((n q)⁻¹ • newCylGrad n q) F q θ φ -
        (2 * (dirVec θ φ ⬝ᵥ ((n q)⁻¹ • newCylGrad n q))) • F q θ φ ∧
    n q ^ 2 • newCylStream n (fun y θ' φ' => (n y ^ 2)⁻¹ • F y θ' φ') q θ φ =
      (Real.sin θ * Real.cos φ) • ((q 0)⁻¹ • pd (fun y => F y θ φ) 1 q) +
        (Real.sin θ * Real.sin φ) • pd (fun y => F y θ φ) 2 q +
        Real.cos θ • ((q 0)⁻¹ • pd (fun y => y 0 • F y θ φ) 0 q) -
        (q 0 * Real.sin θ)⁻¹ • deriv (fun θ' => (Real.sin θ' * Real.cos φ) ^ 2 • F q θ' φ) θ +
        (q 0)⁻¹ • deriv (fun φ' => (Real.cos θ * Real.sin φ' * Real.cos φ') • F q θ φ') φ +
        angularCons ((n q)⁻¹ • newCylGrad n q) F q θ φ := by sorry

end Arxiv1110_5134

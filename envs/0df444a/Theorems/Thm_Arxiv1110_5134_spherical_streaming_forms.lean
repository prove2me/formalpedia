-- Prove2me | Theorems.Thm_Arxiv1110_5134_spherical_streaming_forms
-- name    : Arxiv1110_5134.spherical_streaming_forms
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:19:56.33144+00:00
-- url     : https://prove2.me/theorems/7085f36f-b121-4a29-b1ff-5aca810498ab
-- title:
--   Eqs. (56)-(57): streaming term in spherical coordinates
-- statement:
--   In the spherical coordinates $(\Theta,\Psi,\rho)$ of Fig. 8, with $\boldsymbol\Omega=\mu\mathbf e_\Theta+\eta\mathbf e_\Psi+\xi\mathbf e_\rho$, $\mathbf s_1=-\sin\varphi\,\mathbf e_\Theta+\cos\varphi\,\mathbf e_\Psi$ and $\nabla=\mathbf e_\Theta\rho^{-1}\partial_\Theta+\mathbf e_\Psi(\rho\sin\Theta)^{-1}\partial_\Psi+\mathbf e_\rho\partial_\rho$, let $\partial/\partial s$ be the streaming operator of Eq. (55):
--
--   $$\frac{\partial}{\partial s}=\boldsymbol\Omega\cdot\nabla-\frac{\sin\theta}\rho\frac{\partial}{\partial\theta}-\frac{\eta\cot\Theta}\rho\frac{\partial}{\partial\varphi}+\frac1{\sin\theta}\Big\{\Big[(\xi\boldsymbol\Omega-\mathbf e_\rho)\cdot\frac{\nabla n}n\Big]\frac{\partial}{\partial\theta}+\Big[\mathbf s_1\cdot\frac{\nabla n}n\Big]\frac{\partial}{\partial\varphi}\Big\}.$$
--
--   Assume $\rho>0$, $\sin\Theta\ne0$, $n>0$, $\sin\theta\ne0$, and differentiability of $n$ and $\mathbf I$ at the point. Then the non-conservative form (Eq. 56) holds,
--
--   $$n^2\frac{\partial}{\partial s}\Big[\frac{\mathbf I}{n^2}\Big]=\boldsymbol\Omega\cdot\nabla\mathbf I-\frac{\sin\theta}\rho\frac{\partial\mathbf I}{\partial\theta}-\frac{\eta\cot\Theta}\rho\frac{\partial\mathbf I}{\partial\varphi}+\frac1{\sin\theta}\Big\{\Big[(\xi\boldsymbol\Omega-\mathbf e_\rho)\cdot\frac{\nabla n}n\Big]\frac{\partial\mathbf I}{\partial\theta}+\Big[\mathbf s_1\cdot\frac{\nabla n}n\Big]\frac{\partial\mathbf I}{\partial\varphi}\Big\}-2\Big(\boldsymbol\Omega\cdot\frac{\nabla n}n\Big)\mathbf I,$$
--
--   and so does the conservative form (Eq. 57)
--
--   $$n^2\frac{\partial}{\partial s}\Big[\frac{\mathbf I}{n^2}\Big]=\boldsymbol\Omega\cdot\tilde\nabla\mathbf I-\frac1{\rho\sin\theta}\frac{\partial(\sin^2\theta\,\mathbf I)}{\partial\theta}-\frac{\cot\Theta}\rho\frac{\partial(\eta\mathbf I)}{\partial\varphi}+\frac1{\sin\theta}\Big\{\frac{\partial}{\partial\theta}\Big[\Big((\xi\boldsymbol\Omega-\mathbf e_\rho)\cdot\frac{\nabla n}n\Big)\mathbf I\Big]+\frac{\partial}{\partial\varphi}\Big[\Big(\mathbf s_1\cdot\frac{\nabla n}n\Big)\mathbf I\Big]\Big\},$$
--
--   with $\tilde\nabla(\cdot)=\mathbf e_\Theta(\rho\sin\Theta)^{-1}\partial(\sin\Theta\,\cdot)/\partial\Theta+\mathbf e_\Psi(\rho\sin\Theta)^{-1}\partial(\cdot)/\partial\Psi+\mathbf e_\rho\rho^{-2}\partial(\rho^2\,\cdot)/\partial\rho$.
--
--   **Formalization Note** Eq. (55) is quoted from Ref. [29] and is taken as the definition of $\partial/\partial s$.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c030; Section 4.2.2, Eqs. (55)-(57), PDF pp. 22-23

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem spherical_streaming_forms (n : Vec3 → ℝ) (F : Vec3 → ℝ → ℝ → Stokes)
    (q : Vec3) (θ φ : ℝ) (hρ : 0 < q 2) (hΘ : Real.sin (q 0) ≠ 0) (hn : 0 < n q)
    (hnd : DifferentiableAt ℝ n q)
    (hFq : DifferentiableAt ℝ (fun y => F y θ φ) q)
    (hFθ : DifferentiableAt ℝ (fun θ' => F q θ' φ) θ)
    (hFφ : DifferentiableAt ℝ (fun φ' => F q θ φ') φ) (hθ : Real.sin θ ≠ 0) :
    n q ^ 2 • sphStream n (fun y θ' φ' => (n y ^ 2)⁻¹ • F y θ' φ') q θ φ =
      dirDot θ φ (sphGrad (fun y => F y θ φ) q) -
        (Real.sin θ / q 2) • dTheta F q θ φ -
        (Real.sin θ * Real.sin φ * Real.cot (q 0) / q 2) • dPhi F q θ φ +
        angularStream ((n q)⁻¹ • sphGrad n q) F q θ φ -
        (2 * (dirVec θ φ ⬝ᵥ ((n q)⁻¹ • sphGrad n q))) • F q θ φ ∧
    n q ^ 2 • sphStream n (fun y θ' φ' => (n y ^ 2)⁻¹ • F y θ' φ') q θ φ =
      (Real.sin θ * Real.cos φ) •
          ((q 2 * Real.sin (q 0))⁻¹ • pd (fun y => Real.sin (y 0) • F y θ φ) 0 q) +
        (Real.sin θ * Real.sin φ) • ((q 2 * Real.sin (q 0))⁻¹ • pd (fun y => F y θ φ) 1 q) +
        Real.cos θ • ((q 2 ^ 2)⁻¹ • pd (fun y => y 2 ^ 2 • F y θ φ) 2 q) -
        (q 2 * Real.sin θ)⁻¹ • deriv (fun θ' => Real.sin θ' ^ 2 • F q θ' φ) θ -
        (Real.cot (q 0) / q 2) • deriv (fun φ' => (Real.sin θ * Real.sin φ') • F q θ φ') φ +
        angularCons ((n q)⁻¹ • sphGrad n q) F q θ φ := by sorry

end Arxiv1110_5134

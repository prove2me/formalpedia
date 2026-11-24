-- Prove2me | Theorems.Thm_Arxiv1110_5134_cartesian_streaming_forms
-- name    : Arxiv1110_5134.cartesian_streaming_forms
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:17:35.050223+00:00
-- url     : https://prove2.me/theorems/97fc809f-e936-409c-9529-68bcfa177ea3
-- title:
--   Eqs. (43)-(45): non-conservative and conservative Cartesian streaming terms
-- statement:
--   In Cartesian coordinates, let $\partial/\partial s$ be the Eulerian streaming operator of Eq. (42),
--
--   $$\frac{\partial}{\partial s}=\boldsymbol\Omega\cdot\nabla+\frac1{\sin\theta}\Big\{\Big[(\xi\boldsymbol\Omega-\mathbf k)\cdot\frac{\nabla n}n\Big]\frac{\partial}{\partial\theta}+\Big[\mathbf s_1\cdot\frac{\nabla n}n\Big]\frac{\partial}{\partial\varphi}\Big\}.$$
--
--   Let $n>0$ be differentiable at a point $\mathbf r$, let $\mathbf I(\mathbf r,\theta,\varphi)$ be differentiable in $\mathbf r$, $\theta$ and $\varphi$ there, and let $\sin\theta\ne0$. Then (Eq. 43)
--
--   $$n^2\frac{\partial}{\partial s}\Big[\frac{\mathbf I}{n^2}\Big]=\frac{\partial\mathbf I}{\partial s}-\frac2n\frac{\partial n}{\partial s}\mathbf I,$$
--
--   with $\partial n/\partial s=\boldsymbol\Omega\cdot\nabla n$. In non-conservative form (Eq. 44),
--
--   $$n^2\frac{\partial}{\partial s}\Big[\frac{\mathbf I}{n^2}\Big]=\boldsymbol\Omega\cdot\nabla\mathbf I+\frac1{\sin\theta}\Big\{\Big[(\xi\boldsymbol\Omega-\mathbf k)\cdot\frac{\nabla n}n\Big]\frac{\partial\mathbf I}{\partial\theta}+\Big[\mathbf s_1\cdot\frac{\nabla n}n\Big]\frac{\partial\mathbf I}{\partial\varphi}\Big\}-2\Big(\boldsymbol\Omega\cdot\frac{\nabla n}n\Big)\mathbf I,$$
--
--   and in conservative form (Eq. 45),
--
--   $$n^2\frac{\partial}{\partial s}\Big[\frac{\mathbf I}{n^2}\Big]=\boldsymbol\Omega\cdot\nabla\mathbf I+\frac1{\sin\theta}\Big\{\frac{\partial}{\partial\theta}\Big[\Big((\xi\boldsymbol\Omega-\mathbf k)\cdot\frac{\nabla n}n\Big)\mathbf I\Big]+\frac{\partial}{\partial\varphi}\Big[\Big(\mathbf s_1\cdot\frac{\nabla n}n\Big)\mathbf I\Big]\Big\}.$$
--
--   Here $\boldsymbol\Omega=(\sin\theta\cos\varphi,\sin\theta\sin\varphi,\cos\theta)$, $\xi=\cos\theta$ and $\mathbf s_1=(-\sin\varphi,\cos\varphi,0)$.
--
--   **Formalization Note** Eq. (42) is quoted by the paper from Ref. [26] and is taken as the definition of $\partial/\partial s$.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c026; Section 4.2.2, Eqs. (42)-(45), PDF pp. 19-20

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem cartesian_streaming_forms (n : Vec3 → ℝ) (F : Vec3 → ℝ → ℝ → Stokes) (q : Vec3)
    (θ φ : ℝ) (hn : 0 < n q) (hnd : DifferentiableAt ℝ n q)
    (hFq : DifferentiableAt ℝ (fun y => F y θ φ) q)
    (hFθ : DifferentiableAt ℝ (fun θ' => F q θ' φ) θ)
    (hFφ : DifferentiableAt ℝ (fun φ' => F q θ φ') φ) (hθ : Real.sin θ ≠ 0) :
    n q ^ 2 • cartStream n (fun y θ' φ' => (n y ^ 2)⁻¹ • F y θ' φ') q θ φ =
      cartStream n F q θ φ - (2 / n q * dirDot θ φ (cartGrad n q)) • F q θ φ ∧
    n q ^ 2 • cartStream n (fun y θ' φ' => (n y ^ 2)⁻¹ • F y θ' φ') q θ φ =
      dirDot θ φ (cartGrad (fun y => F y θ φ) q) +
        angularStream ((n q)⁻¹ • cartGrad n q) F q θ φ -
        (2 * (dirVec θ φ ⬝ᵥ ((n q)⁻¹ • cartGrad n q))) • F q θ φ ∧
    n q ^ 2 • cartStream n (fun y θ' φ' => (n y ^ 2)⁻¹ • F y θ' φ') q θ φ =
      dirDot θ φ (cartGrad (fun y => F y θ φ) q) +
        angularCons ((n q)⁻¹ • cartGrad n q) F q θ φ := by sorry

end Arxiv1110_5134

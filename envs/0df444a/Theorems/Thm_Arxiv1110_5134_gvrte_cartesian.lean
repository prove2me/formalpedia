-- Prove2me | Theorems.Thm_Arxiv1110_5134_gvrte_cartesian
-- name    : Arxiv1110_5134.gvrte_cartesian
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T09:18:09.405181+00:00
-- url     : https://prove2.me/theorems/a368a754-cc70-4fb1-8536-51eaafa6c8f8
-- title:
--   Eq. (48): the Cartesian conservative form of the transient GVRTE
-- statement:
--   Under the hypotheses of Eqs. (43)-(45) at a point $(t,\mathbf r,\theta,\varphi)$, with $c>0$: the Eulerian GVRTE (Eq. 41), with $n^2\partial_s[\mathbf I/n^2]$ computed by the Cartesian streaming operator of Eq. (42), holds if and only if the Cartesian conservative form (Eq. 48) holds:
--
--   $$\frac nc\frac{\partial\mathbf I}{\partial t}+\boldsymbol\Omega\cdot\nabla\mathbf I+\frac1{\sin\theta}\Big\{\frac{\partial}{\partial\theta}\Big[\Big((\xi\boldsymbol\Omega-\mathbf k)\cdot\frac{\nabla n}n\Big)\mathbf I\Big]+\frac{\partial}{\partial\varphi}\Big[\Big(\mathbf s_1\cdot\frac{\nabla n}n\Big)\mathbf I\Big]\Big\}+(\boldsymbol\kappa_e+\mathbf R)\mathbf I=\boldsymbol\kappa_a\mathbf I_b+\frac1{4\pi}\int_{4\pi}\mathbf Z(\boldsymbol\Omega',\boldsymbol\Omega)\mathbf I(t,\mathbf r,\boldsymbol\Omega')\,d\Omega'.$$
--
--   **Formalization Note** The torsion $\kappa$ in $\mathbf R$ is a given number at the point; its formula is Eq. (47). The incident field in the integral is an arbitrary function of direction.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c017; Section 4.2.2, Eq. (48), PDF p. 20

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem gvrte_cartesian (n : Vec3 → ℝ) (c : ℝ) (hc : 0 < c)
    (F : ℝ → Vec3 → ℝ → ℝ → Stokes) (t : ℝ) (q : Vec3) (θ φ : ℝ)
    (hn : 0 < n q) (hnd : DifferentiableAt ℝ n q)
    (hFq : DifferentiableAt ℝ (fun y => F t y θ φ) q)
    (hFθ : DifferentiableAt ℝ (fun θ' => F t q θ' φ) θ)
    (hFφ : DifferentiableAt ℝ (fun φ' => F t q θ φ') φ) (hθ : Real.sin θ ≠ 0)
    (κe κa : Matrix (Fin 4) (Fin 4) ℝ) (κ : ℝ) (Ib : Stokes)
    (Z : Dir → Matrix (Fin 4) (Fin 4) ℝ) (L : Dir → Stokes) :
    (n q / c) • deriv (fun t' => F t' q θ φ) t +
        n q ^ 2 • cartStream n (fun y θ' φ' => (n y ^ 2)⁻¹ • F t y θ' φ') q θ φ +
        (κe + rytovMatrix κ) *ᵥ F t q θ φ = κa *ᵥ Ib + scatSource Z L ↔
      (n q / c) • deriv (fun t' => F t' q θ φ) t +
        dirDot θ φ (cartGrad (fun y => F t y θ φ) q) +
        angularCons ((n q)⁻¹ • cartGrad n q) (F t) q θ φ +
        (κe + rytovMatrix κ) *ᵥ F t q θ φ = κa *ᵥ Ib + scatSource Z L := by sorry

end Arxiv1110_5134

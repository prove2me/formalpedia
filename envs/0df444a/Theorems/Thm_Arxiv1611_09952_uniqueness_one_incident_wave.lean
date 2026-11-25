-- Prove2me | Theorems.Thm_Arxiv1611_09952_uniqueness_one_incident_wave
-- name    : Arxiv1611_09952.uniqueness_one_incident_wave
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T00:12:21.783304+00:00
-- url     : https://prove2.me/theorems/66c89266-e8c4-43e9-8fc0-f6dae5110b9f
-- title:
--   Theorem 1: $S$ and the boundary condition are determined by $A(\beta,\alpha_0,k_0)$ on a solid angle
-- statement:
--   Let $k>0$, let $\alpha_0\in S^2$, and let $D_1,D_2$ be obstacles (bounded domains in $\mathbb{R}^3$ with connected $C^2$ boundaries $S_1,S_2$) with admissible boundary conditions $\Gamma^{(1)},\Gamma^{(2)}$, each Dirichlet, Neumann or impedance ($h$ constant, $\operatorname{Im}h\ge0$, $h\neq0$). Let $u_m$ be the scattering solution of problem (1)-(2) for $D_m$, $\Gamma^{(m)}$, wave number $k$ and incident direction $\alpha_0$, and let $A_m(\beta)=A_m(\beta,\alpha_0,k)$ be its scattering amplitude. Suppose there is a solid angle, i.e. a nonempty open subset $\Omega\subset S^2$, such that $A_1(\beta)=A_2(\beta)$ for all $\beta\in\Omega$. Then
--
--   $$S_1=S_2\qquad\text{and}\qquad\Gamma^{(1)}=\Gamma^{(2)}.$$
--
--   In words, the surface of the obstacle and the boundary condition on it are uniquely determined by the scattering amplitude for one incident direction and one wave number, known on a solid angle of scattering directions.
--
--   **Formalization Note** The theorem as printed does not name $\alpha_0$ and $k_0$; the abstract and eq. (17) fix them. Uniqueness is stated as: any two admissible obstacles whose amplitudes agree on the solid angle have the same surface and the same boundary condition.
-- source:
--   A. G. Ramm, Inverse obstacle scattering with non-over-determined data, arXiv:1611.09952v2 (2017), claim c001; Section 1, Theorem 1, PDF p. 3 (Abstract, PDF p. 1); proof in Section 2, Proof of Theorem 1, eq. (25), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1611_09952_Basic

open MeasureTheory Filter Topology Asymptotics

namespace Arxiv1611_09952

theorem uniqueness_one_incident_wave (k : ℝ) (hk : 0 < k) (α₀ : E3)
    (hα₀ : α₀ ∈ Metric.sphere (0 : E3) 1) (D₁ D₂ : Set E3)
    (hD₁ : IsObstacle D₁) (hD₂ : IsObstacle D₂) (bc₁ bc₂ : BoundaryCondition)
    (hbc₁ : bc₁.Admissible) (hbc₂ : bc₂.Admissible) (u₁ u₂ : E3 → ℂ)
    (hu₁ : IsScatteringSolution D₁ bc₁ k α₀ u₁) (hu₂ : IsScatteringSolution D₂ bc₂ k α₀ u₂)
    (A₁ A₂ : E3 → ℂ) (hA₁ : HasScatteringAmplitude k α₀ u₁ A₁)
    (hA₂ : HasScatteringAmplitude k α₀ u₂ A₂)
    (U : Set E3) (hU : IsOpen U) (hUne : (U ∩ Metric.sphere (0 : E3) 1).Nonempty)
    (hA : ∀ β ∈ U ∩ Metric.sphere (0 : E3) 1, A₁ β = A₂ β) :
    frontier D₁ = frontier D₂ ∧ bc₁ = bc₂ := by sorry

end Arxiv1611_09952

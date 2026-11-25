-- Prove2me | Theorems.Thm_Arxiv1611_09952_boundary_condition_recovery
-- name    : Arxiv1611_09952.boundary_condition_recovery
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T00:03:05.769347+00:00
-- url     : https://prove2.me/theorems/c17042cf-1183-4f0e-832b-9d56191cd79e
-- title:
--   Theorem 1 (proof, final step): once $S$ is known, the boundary condition is determined
-- statement:
--   Let $k>0$, let $\alpha_0\in S^2$, and let $D_1,D_2$ be obstacles (bounded domains in $\mathbb{R}^3$ with connected $C^2$ boundaries $S_1,S_2$) with admissible boundary conditions $\Gamma^{(1)},\Gamma^{(2)}$, each Dirichlet, Neumann or impedance ($h$ constant, $\operatorname{Im}h\ge0$, $h\neq0$). Let $u_m$ be the scattering solution of problem (1)-(2) for $D_m$, $\Gamma^{(m)}$, wave number $k$ and incident direction $\alpha_0$, and let $A_m(\beta)=A_m(\beta,\alpha_0,k)$ be its scattering amplitude. Suppose $A_1(\beta)=A_2(\beta)$ for all $\beta\in S^2$ and $S_1=S_2$. Then $D_1=D_2=:D$, $u_1=u_2$ on $D'$, and the boundary conditions coincide: $\Gamma^{(1)}=\Gamma^{(2)}$.
--
--   This is the final step of the proof of Theorem 1: once the surface is known, the type of the boundary condition (and the impedance $h=-u_N/u$) is read off from the common field $u$ on $S$.
-- source:
--   A. G. Ramm, Inverse obstacle scattering with non-over-determined data, arXiv:1611.09952v2 (2017), claim c010; Section 2, Proof of Theorem 1, final paragraph, PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1611_09952_Basic

open MeasureTheory Filter Topology Asymptotics

namespace Arxiv1611_09952

theorem boundary_condition_recovery (k : ℝ) (hk : 0 < k) (α₀ : E3)
    (hα₀ : α₀ ∈ Metric.sphere (0 : E3) 1) (D₁ D₂ : Set E3)
    (hD₁ : IsObstacle D₁) (hD₂ : IsObstacle D₂) (bc₁ bc₂ : BoundaryCondition)
    (hbc₁ : bc₁.Admissible) (hbc₂ : bc₂.Admissible) (u₁ u₂ : E3 → ℂ)
    (hu₁ : IsScatteringSolution D₁ bc₁ k α₀ u₁) (hu₂ : IsScatteringSolution D₂ bc₂ k α₀ u₂)
    (A₁ A₂ : E3 → ℂ) (hA₁ : HasScatteringAmplitude k α₀ u₁ A₁)
    (hA₂ : HasScatteringAmplitude k α₀ u₂ A₂)
    (hA : ∀ β ∈ Metric.sphere (0 : E3) 1, A₁ β = A₂ β) (hS : frontier D₁ = frontier D₂) :
    D₁ = D₂ ∧ (∀ x ∈ D₁ᶜ, u₁ x = u₂ x) ∧ bc₁ = bc₂ := by sorry

end Arxiv1611_09952

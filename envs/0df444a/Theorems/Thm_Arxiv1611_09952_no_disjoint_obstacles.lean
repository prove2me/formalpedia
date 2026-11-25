-- Prove2me | Theorems.Thm_Arxiv1611_09952_no_disjoint_obstacles
-- name    : Arxiv1611_09952.no_disjoint_obstacles
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T00:06:01.27991+00:00
-- url     : https://prove2.me/theorems/a5dc2779-a8ab-456c-88be-f2ee00c4ab78
-- title:
--   Theorem 2: obstacles with disjoint closures cannot have the same amplitude
-- statement:
--   Let $k>0$, let $\alpha_0\in S^2$, and let $D_1,D_2$ be obstacles (bounded domains in $\mathbb{R}^3$ with connected $C^2$ boundaries $S_1,S_2$) with admissible boundary conditions $\Gamma^{(1)},\Gamma^{(2)}$, each Dirichlet, Neumann or impedance ($h$ constant, $\operatorname{Im}h\ge0$, $h\neq0$). Let $u_m$ be the scattering solution of problem (1)-(2) for $D_m$, $\Gamma^{(m)}$, wave number $k$ and incident direction $\alpha_0$, and let $A_m(\beta)=A_m(\beta,\alpha_0,k)$ be its scattering amplitude. Suppose there is a solid angle, i.e. a nonempty open subset $\Omega\subset S^2$, such that $A_1(\beta)=A_2(\beta)$ for all $\beta\in\Omega$. Then it is not possible that $D_1\neq D_2$ and $\overline{D_1}\cap\overline{D_2}=\emptyset$.
--
--   This is the case of Theorem 1 in which $S_1$ and $S_2$ do not intersect and neither lies inside the other.
--
--   **Formalization Note** The printed theorem has the hypothesis $D_1\cap D_2=\emptyset$. Section 1 assigns to Theorem 2 exactly the case where $S_1$ does not intersect $S_2$ and does not lie inside it, and the proof needs $u_1$ to be defined on all of $\overline{D_2}$; so the obstacles are required to have disjoint closures ($D_1\cap D_2=\emptyset$ and $S_1\cap S_2=\emptyset$). Obstacles that touch belong to the first case (Theorem 1).
-- source:
--   A. G. Ramm, Inverse obstacle scattering with non-over-determined data, arXiv:1611.09952v2 (2017), claim c002; Section 1, Theorem 2, PDF p. 3, with the case hypothesis $S_1\cap S_2=\emptyset$ of Section 1 ("the second case"), PDF p. 3; proof in Section 2, Proof of Theorem 2, PDF p. 9

import Mathlib
import Definitions.Def_Arxiv1611_09952_Basic

open MeasureTheory Filter Topology Asymptotics

namespace Arxiv1611_09952

theorem no_disjoint_obstacles (k : ℝ) (hk : 0 < k) (α₀ : E3)
    (hα₀ : α₀ ∈ Metric.sphere (0 : E3) 1) (D₁ D₂ : Set E3)
    (hD₁ : IsObstacle D₁) (hD₂ : IsObstacle D₂) (bc₁ bc₂ : BoundaryCondition)
    (hbc₁ : bc₁.Admissible) (hbc₂ : bc₂.Admissible) (u₁ u₂ : E3 → ℂ)
    (hu₁ : IsScatteringSolution D₁ bc₁ k α₀ u₁) (hu₂ : IsScatteringSolution D₂ bc₂ k α₀ u₂)
    (A₁ A₂ : E3 → ℂ) (hA₁ : HasScatteringAmplitude k α₀ u₁ A₁)
    (hA₂ : HasScatteringAmplitude k α₀ u₂ A₂)
    (U : Set E3) (hU : IsOpen U) (hUne : (U ∩ Metric.sphere (0 : E3) 1).Nonempty)
    (hA : ∀ β ∈ U ∩ Metric.sphere (0 : E3) 1, A₁ β = A₂ β) :
    ¬ (D₁ ≠ D₂ ∧ closure D₁ ∩ closure D₂ = ∅) := by sorry

end Arxiv1611_09952

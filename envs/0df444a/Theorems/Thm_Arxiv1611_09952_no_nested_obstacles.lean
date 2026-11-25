-- Prove2me | Theorems.Thm_Arxiv1611_09952_no_nested_obstacles
-- name    : Arxiv1611_09952.no_nested_obstacles
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T00:08:57.774006+00:00
-- url     : https://prove2.me/theorems/e19bf425-21c1-45d6-9936-1d381d472af3
-- title:
--   Theorem 3: nested obstacles cannot have the same amplitude
-- statement:
--   Let $k>0$, let $\alpha_0\in S^2$, and let $D_1,D_2$ be obstacles (bounded domains in $\mathbb{R}^3$ with connected $C^2$ boundaries $S_1,S_2$) with admissible boundary conditions $\Gamma^{(1)},\Gamma^{(2)}$, each Dirichlet, Neumann or impedance ($h$ constant, $\operatorname{Im}h\ge0$, $h\neq0$). Let $u_m$ be the scattering solution of problem (1)-(2) for $D_m$, $\Gamma^{(m)}$, wave number $k$ and incident direction $\alpha_0$, and let $A_m(\beta)=A_m(\beta,\alpha_0,k)$ be its scattering amplitude. Suppose there is a solid angle, i.e. a nonempty open subset $\Omega\subset S^2$, such that $A_1(\beta)=A_2(\beta)$ for all $\beta\in\Omega$. Then it is not possible that $D_1\neq D_2$ and $D_1\subset D_2$.
--
--   This is the case of Theorem 1 in which one obstacle lies inside the other.
--
--   **Formalization Note** The statement is the printed one, $D_1\subset D_2$, so it also covers nested obstacles whose boundaries touch, which Section 1 assigns to Theorem 1 (the intended case of Theorem 3 has $S_1\cap S_2=\emptyset$). The paper's proof of Theorem 3, via Lemma 4, does not use the separation.
-- source:
--   A. G. Ramm, Inverse obstacle scattering with non-over-determined data, arXiv:1611.09952v2 (2017), claim c003; Section 1, Theorem 3, PDF p. 3; proof in Section 2, Proof of Theorem 3, eqs. (28)-(30), PDF p. 9

import Mathlib
import Definitions.Def_Arxiv1611_09952_Basic

open MeasureTheory Filter Topology Asymptotics

namespace Arxiv1611_09952

theorem no_nested_obstacles (k : ℝ) (hk : 0 < k) (α₀ : E3)
    (hα₀ : α₀ ∈ Metric.sphere (0 : E3) 1) (D₁ D₂ : Set E3)
    (hD₁ : IsObstacle D₁) (hD₂ : IsObstacle D₂) (bc₁ bc₂ : BoundaryCondition)
    (hbc₁ : bc₁.Admissible) (hbc₂ : bc₂.Admissible) (u₁ u₂ : E3 → ℂ)
    (hu₁ : IsScatteringSolution D₁ bc₁ k α₀ u₁) (hu₂ : IsScatteringSolution D₂ bc₂ k α₀ u₂)
    (A₁ A₂ : E3 → ℂ) (hA₁ : HasScatteringAmplitude k α₀ u₁ A₁)
    (hA₂ : HasScatteringAmplitude k α₀ u₂ A₂)
    (U : Set E3) (hU : IsOpen U) (hUne : (U ∩ Metric.sphere (0 : E3) 1).Nonempty)
    (hA : ∀ β ∈ U ∩ Metric.sphere (0 : E3) 1, A₁ β = A₂ β) :
    ¬ (D₁ ≠ D₂ ∧ D₁ ⊆ D₂) := by sorry

end Arxiv1611_09952

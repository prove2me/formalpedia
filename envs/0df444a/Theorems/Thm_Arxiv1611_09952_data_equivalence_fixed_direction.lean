-- Prove2me | Theorems.Thm_Arxiv1611_09952_data_equivalence_fixed_direction
-- name    : Arxiv1611_09952.data_equivalence_fixed_direction
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T00:01:00.942803+00:00
-- url     : https://prove2.me/theorems/606e4702-2446-4da5-aca6-b927300e4a66
-- title:
--   Eqs. (26)-(27): $G(\cdot,y_0)$, $u(\cdot,\alpha_0)$ and $A(\cdot,\alpha_0)$ determine one another
-- statement:
--   Let $k>0$ and let $D_1,D_2$ be obstacles (bounded domains in $\mathbb{R}^3$ with connected $C^2$ boundaries $S_1,S_2$), both with the Dirichlet condition. Let $G_m$ be the Dirichlet Green's function of $D_m'$, fix $\alpha_0\in S^2$, let $u_m=u_m(\cdot,\alpha_0)$ be the scattering solution and $A_m(\beta)=A_m(\beta,\alpha_0)$ its amplitude, and let $\eta$ be a vector with $\eta\cdot\alpha_0=0$. Say that the Green's functions agree on the line $y_0=-\tau\alpha_0+\eta$ if $G_1(x,y_0)=G_2(x,y_0)$ for every $\tau>0$ with $y_0\in D_{12}'$ and every $x\in D_{12}'$, $x\ne y_0$. The implications (26) $G(\cdot,y_0)\to u(\cdot,\alpha_0)\to A(\cdot,\alpha_0)$ and (27) $A(\cdot,\alpha_0)\to u(\cdot,\alpha_0)\to G(\cdot,y_0)$ hold:
--
--   1. if the Green's functions agree on the line, then $u_1=u_2$ on $D_{12}'$;
--   2. if $u_1=u_2$ on $D_{12}'$, then $A_1=A_2$ on $S^2$;
--   3. if $A_1=A_2$ on $S^2$, then $u_1=u_2$ on $D_{12}'$;
--   4. if $u_1=u_2$ on $D_{12}'$, then the Green's functions agree on the line.
--
--   **Formalization Note** As in (23)-(24), "determines" is stated for two obstacles on their common exterior. The vector $\eta$ is arbitrary but fixed, so the statement is made for each such $\eta$.
-- source:
--   A. G. Ramm, Inverse obstacle scattering with non-over-determined data, arXiv:1611.09952v2 (2017), claim c011; Section 2, implications (26) and (27), PDF p. 9

import Mathlib
import Definitions.Def_Arxiv1611_09952_Basic

open MeasureTheory Filter Topology Asymptotics

namespace Arxiv1611_09952

theorem data_equivalence_fixed_direction (k : ℝ) (hk : 0 < k) (D₁ D₂ : Set E3)
    (hD₁ : IsObstacle D₁) (hD₂ : IsObstacle D₂) (G₁ G₂ : E3 → E3 → ℂ)
    (hG₁ : IsDirichletGreen D₁ k G₁) (hG₂ : IsDirichletGreen D₂ k G₂)
    (α₀ : E3) (hα₀ : α₀ ∈ Metric.sphere (0 : E3) 1) (u₁ u₂ : E3 → ℂ)
    (hu₁ : IsScatteringSolution D₁ .dirichlet k α₀ u₁)
    (hu₂ : IsScatteringSolution D₂ .dirichlet k α₀ u₂)
    (A₁ A₂ : E3 → ℂ) (hA₁ : HasScatteringAmplitude k α₀ u₁ A₁)
    (hA₂ : HasScatteringAmplitude k α₀ u₂ A₂) (η : E3) (hη : inner ℝ α₀ η = 0) :
    ((∀ τ : ℝ, 0 < τ → ∀ x ∈ (D₁ ∪ D₂)ᶜ, (-τ) • α₀ + η ∈ (D₁ ∪ D₂)ᶜ → x ≠ (-τ) • α₀ + η →
        G₁ x ((-τ) • α₀ + η) = G₂ x ((-τ) • α₀ + η)) →
      ∀ x ∈ (D₁ ∪ D₂)ᶜ, u₁ x = u₂ x) ∧
    ((∀ x ∈ (D₁ ∪ D₂)ᶜ, u₁ x = u₂ x) → ∀ β ∈ Metric.sphere (0 : E3) 1, A₁ β = A₂ β) ∧
    ((∀ β ∈ Metric.sphere (0 : E3) 1, A₁ β = A₂ β) → ∀ x ∈ (D₁ ∪ D₂)ᶜ, u₁ x = u₂ x) ∧
    ((∀ x ∈ (D₁ ∪ D₂)ᶜ, u₁ x = u₂ x) →
      ∀ τ : ℝ, 0 < τ → ∀ x ∈ (D₁ ∪ D₂)ᶜ, (-τ) • α₀ + η ∈ (D₁ ∪ D₂)ᶜ → x ≠ (-τ) • α₀ + η →
        G₁ x ((-τ) • α₀ + η) = G₂ x ((-τ) • α₀ + η)) := by sorry

end Arxiv1611_09952

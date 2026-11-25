-- Prove2me | Theorems.Thm_Arxiv1611_09952_data_equivalence_all_directions
-- name    : Arxiv1611_09952.data_equivalence_all_directions
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T23:59:01.069782+00:00
-- url     : https://prove2.me/theorems/60daad90-90d5-42ba-8020-b371f8f668b0
-- title:
--   Eqs. (23)-(24): $G$, $u$ and $A$ determine one another at fixed $k$
-- statement:
--   Let $k>0$ and let $D_1,D_2$ be obstacles (bounded domains in $\mathbb{R}^3$ with connected $C^2$ boundaries $S_1,S_2$), both with the Dirichlet condition. Let $G_m$ be the Dirichlet Green's function of $D_m'$, and for every $\alpha\in S^2$ let $u_m(\cdot,\alpha)$ be the scattering solution and $A_m(\beta,\alpha)$ its amplitude; $D_{12}'=\mathbb{R}^3\setminus(D_1\cup D_2)$. The implications (23) $G\to u\to A$ and (24) $A\to u\to G$ hold at fixed $k$:
--
--   1. if $G_1=G_2$ off the diagonal of $D_{12}'\times D_{12}'$, then $u_1(\cdot,\alpha)=u_2(\cdot,\alpha)$ on $D_{12}'$ for every $\alpha\in S^2$;
--   2. if $u_1(\cdot,\alpha)=u_2(\cdot,\alpha)$ on $D_{12}'$ for every $\alpha$, then $A_1=A_2$ on $S^2\times S^2$;
--   3. if $A_1=A_2$ on $S^2\times S^2$, then $u_1(\cdot,\alpha)=u_2(\cdot,\alpha)$ on $D_{12}'$ for every $\alpha$;
--   4. if $u_1(\cdot,\alpha)=u_2(\cdot,\alpha)$ on $D_{12}'$ for every $\alpha$, then $G_1=G_2$ off the diagonal of $D_{12}'\times D_{12}'$.
--
--   **Formalization Note** "$X$ determines $Y$" is stated, as in the paper's own justification, for two obstacles: equality of the $X$-data on the common exterior $D_{12}'$ implies equality of the $Y$-data there.
-- source:
--   A. G. Ramm, Inverse obstacle scattering with non-over-determined data, arXiv:1611.09952v2 (2017), claim c009; Section 2, implications (23) and (24), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1611_09952_Basic

open MeasureTheory Filter Topology Asymptotics

namespace Arxiv1611_09952

theorem data_equivalence_all_directions (k : ℝ) (hk : 0 < k) (D₁ D₂ : Set E3)
    (hD₁ : IsObstacle D₁) (hD₂ : IsObstacle D₂) (G₁ G₂ : E3 → E3 → ℂ)
    (hG₁ : IsDirichletGreen D₁ k G₁) (hG₂ : IsDirichletGreen D₂ k G₂) (u₁ u₂ : E3 → E3 → ℂ)
    (hu₁ : ∀ α ∈ Metric.sphere (0 : E3) 1, IsScatteringSolution D₁ .dirichlet k α (u₁ α))
    (hu₂ : ∀ α ∈ Metric.sphere (0 : E3) 1, IsScatteringSolution D₂ .dirichlet k α (u₂ α))
    (A₁ A₂ : E3 → E3 → ℂ)
    (hA₁ : ∀ α ∈ Metric.sphere (0 : E3) 1, HasScatteringAmplitude k α (u₁ α) (fun β => A₁ β α))
    (hA₂ : ∀ α ∈ Metric.sphere (0 : E3) 1, HasScatteringAmplitude k α (u₂ α) (fun β => A₂ β α)) :
    ((∀ x ∈ (D₁ ∪ D₂)ᶜ, ∀ y ∈ (D₁ ∪ D₂)ᶜ, x ≠ y → G₁ x y = G₂ x y) →
      ∀ α ∈ Metric.sphere (0 : E3) 1, ∀ x ∈ (D₁ ∪ D₂)ᶜ, u₁ α x = u₂ α x) ∧
    ((∀ α ∈ Metric.sphere (0 : E3) 1, ∀ x ∈ (D₁ ∪ D₂)ᶜ, u₁ α x = u₂ α x) →
      ∀ β ∈ Metric.sphere (0 : E3) 1, ∀ α ∈ Metric.sphere (0 : E3) 1, A₁ β α = A₂ β α) ∧
    ((∀ β ∈ Metric.sphere (0 : E3) 1, ∀ α ∈ Metric.sphere (0 : E3) 1, A₁ β α = A₂ β α) →
      ∀ α ∈ Metric.sphere (0 : E3) 1, ∀ x ∈ (D₁ ∪ D₂)ᶜ, u₁ α x = u₂ α x) ∧
    ((∀ α ∈ Metric.sphere (0 : E3) 1, ∀ x ∈ (D₁ ∪ D₂)ᶜ, u₁ α x = u₂ α x) →
      ∀ x ∈ (D₁ ∪ D₂)ᶜ, ∀ y ∈ (D₁ ∪ D₂)ᶜ, x ≠ y → G₁ x y = G₂ x y) := by sorry

end Arxiv1611_09952

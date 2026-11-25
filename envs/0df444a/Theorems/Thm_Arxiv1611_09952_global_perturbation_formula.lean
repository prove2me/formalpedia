-- Prove2me | Theorems.Thm_Arxiv1611_09952_global_perturbation_formula
-- name    : Arxiv1611_09952.global_perturbation_formula
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T23:51:30.525904+00:00
-- url     : https://prove2.me/theorems/49e867dc-0250-4da9-a97d-fd0071bdd03b
-- title:
--   Lemma 2: global perturbation formula
-- statement:
--   Let $k>0$ and let $D_1,D_2$ be obstacles (bounded domains in $\mathbb{R}^3$ with connected $C^2$ boundaries $S_1,S_2$), both with the Dirichlet condition. For $m=1,2$ and every $\alpha\in S^2$ let $u_m(\cdot,\alpha)$ be the scattering solution for $D_m$ and $A_m(\beta,\alpha)$ its amplitude. Let $D_{12}=D_1\cup D_2$, $S_{12}=\partial D_{12}$, and let $N$ be the unit normal to $S_{12}$ pointing out of $D_{12}$. Then for all $\alpha,\beta\in S^2$
--
--   $$4\pi\,[A_1(\beta,\alpha)-A_2(\beta,\alpha)]=\int_{S_{12}}\big[u_1(s,\alpha)\,u_{2N}(s,-\beta)-u_{1N}(s,\alpha)\,u_2(s,-\beta)\big]\,ds,$$
--
--   where $u_{mN}$ is the normal derivative taken from the exterior of $D_m$ and $ds$ is surface area on $S_{12}$.
--
--   The formula expresses the difference of two amplitudes as a boundary integral over the outer boundary of the union of the obstacles.
--
--   **Formalization Note** The paper defines the integral over the possibly non-smooth surface $S_{12}$ as a limit over $S_{12}\setminus S_\epsilon$ (Remark 1); here it is the Lebesgue integral with respect to area on $S_{12}$, which agrees with that limit for a bounded integrand. Where $S_{12}$ has no normal (on $S_1\cap S_2$) the integrand vanishes because $u_1=u_2=0$ there. Lemma 2 belongs to Section 2, where the Dirichlet condition is assumed for definiteness.
-- source:
--   A. G. Ramm, Inverse obstacle scattering with non-over-determined data, arXiv:1611.09952v2 (2017), claim c005; Section 2, Lemma 2, eq. (6), PDF p. 5 (proof eqs. (7)-(10); Remark 1, PDF p. 5)

import Mathlib
import Definitions.Def_Arxiv1611_09952_Basic

open MeasureTheory Filter Topology Asymptotics

namespace Arxiv1611_09952

theorem global_perturbation_formula (k : ℝ) (hk : 0 < k) (D₁ D₂ : Set E3)
    (hD₁ : IsObstacle D₁) (hD₂ : IsObstacle D₂) (u₁ u₂ : E3 → E3 → ℂ)
    (hu₁ : ∀ α ∈ Metric.sphere (0 : E3) 1, IsScatteringSolution D₁ .dirichlet k α (u₁ α))
    (hu₂ : ∀ α ∈ Metric.sphere (0 : E3) 1, IsScatteringSolution D₂ .dirichlet k α (u₂ α))
    (A₁ A₂ : E3 → E3 → ℂ)
    (hA₁ : ∀ α ∈ Metric.sphere (0 : E3) 1, HasScatteringAmplitude k α (u₁ α) (fun β => A₁ β α))
    (hA₂ : ∀ α ∈ Metric.sphere (0 : E3) 1, HasScatteringAmplitude k α (u₂ α) (fun β => A₂ β α)) :
    ∀ β ∈ Metric.sphere (0 : E3) 1, ∀ α ∈ Metric.sphere (0 : E3) 1,
      4 * (Real.pi : ℂ) * (A₁ β α - A₂ β α) =
        ∫ s, (u₁ α s * boundaryDeriv (openExterior D₂) (outerNormal (D₁ ∪ D₂) s) (u₂ (-β)) s -
            boundaryDeriv (openExterior D₁) (outerNormal (D₁ ∪ D₂) s) (u₁ α) s * u₂ (-β) s)
          ∂(surfaceMeasure (frontier (D₁ ∪ D₂))) := by sorry

end Arxiv1611_09952

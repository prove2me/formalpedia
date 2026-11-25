-- Prove2me | Theorems.Thm_Arxiv1611_09952_lifting_lemma
-- name    : Arxiv1611_09952.lifting_lemma
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T23:54:29.536878+00:00
-- url     : https://prove2.me/theorems/2191bd2e-1e66-47e0-9103-8494ca95cdda
-- title:
--   Lemma 4: lifting lemma
-- statement:
--   Let $k>0$ and let $D_1,D_2$ be obstacles (bounded domains in $\mathbb{R}^3$ with connected $C^2$ boundaries $S_1,S_2$), both with the Dirichlet condition. Let $G_m$ be the Dirichlet Green's function of $D_m'$, and for every $\alpha\in S^2$ let $u_m(\cdot,\alpha)$ be the scattering solution and $A_m(\beta,\alpha)$ its amplitude. Let $D_{12}'=\mathbb{R}^3\setminus(D_1\cup D_2)$.
--
--   1. If $A_1(\beta,\alpha)=A_2(\beta,\alpha)$ for all $\beta,\alpha\in S^2$, then $G_1(x,y)=G_2(x,y)$ for all $x\neq y$ in $D_{12}'$.
--   2. If $\alpha_0\in S^2$ and $A_1(\beta,\alpha_0)=A_2(\beta,\alpha_0)$ for all $\beta\in S^2$, then for every $\eta$ with $\eta\cdot\alpha_0=0$ and every $\tau>0$, with $y_0=-\tau\alpha_0+\eta$,
--   $$G_1(x,y_0)=G_2(x,y_0)\qquad\text{for all }x\in D_{12}',\ x\neq y_0,$$
--   whenever $y_0\in D_{12}'$.
--
--   Part 2 is the step on which the proofs of Theorems 1 and 3 rest.
--
--   **Formalization Note** The printed statement says that $\tau>0$ "is a number"; it is stated here for every $\tau>0$, which is how it is used in eqs. (25) and (28). The conditions $y_0\in D_{12}'$ and $x\ne y_0$ are implicit in the paper, since $G_m(x,y_0)$ is defined only for $x\ne y_0$ outside $D_m$ (eq. (28) states $y_0\in D_2'$ explicitly).
-- source:
--   A. G. Ramm, Inverse obstacle scattering with non-over-determined data, arXiv:1611.09952v2 (2017), claim c007; Section 2, Lemma 4, PDF p. 6 (proof eqs. (11)-(20), PDF pp. 6-7)

import Mathlib
import Definitions.Def_Arxiv1611_09952_Basic

open MeasureTheory Filter Topology Asymptotics

namespace Arxiv1611_09952

theorem lifting_lemma (k : ℝ) (hk : 0 < k) (D₁ D₂ : Set E3)
    (hD₁ : IsObstacle D₁) (hD₂ : IsObstacle D₂) (G₁ G₂ : E3 → E3 → ℂ)
    (hG₁ : IsDirichletGreen D₁ k G₁) (hG₂ : IsDirichletGreen D₂ k G₂) (u₁ u₂ : E3 → E3 → ℂ)
    (hu₁ : ∀ α ∈ Metric.sphere (0 : E3) 1, IsScatteringSolution D₁ .dirichlet k α (u₁ α))
    (hu₂ : ∀ α ∈ Metric.sphere (0 : E3) 1, IsScatteringSolution D₂ .dirichlet k α (u₂ α))
    (A₁ A₂ : E3 → E3 → ℂ)
    (hA₁ : ∀ α ∈ Metric.sphere (0 : E3) 1, HasScatteringAmplitude k α (u₁ α) (fun β => A₁ β α))
    (hA₂ : ∀ α ∈ Metric.sphere (0 : E3) 1, HasScatteringAmplitude k α (u₂ α) (fun β => A₂ β α)) :
    ((∀ β ∈ Metric.sphere (0 : E3) 1, ∀ α ∈ Metric.sphere (0 : E3) 1, A₁ β α = A₂ β α) →
      ∀ x ∈ (D₁ ∪ D₂)ᶜ, ∀ y ∈ (D₁ ∪ D₂)ᶜ, x ≠ y → G₁ x y = G₂ x y) ∧
    (∀ α₀ ∈ Metric.sphere (0 : E3) 1,
      (∀ β ∈ Metric.sphere (0 : E3) 1, A₁ β α₀ = A₂ β α₀) →
      ∀ η : E3, inner ℝ α₀ η = 0 → ∀ τ : ℝ, 0 < τ →
        ∀ x ∈ (D₁ ∪ D₂)ᶜ, (-τ) • α₀ + η ∈ (D₁ ∪ D₂)ᶜ → x ≠ (-τ) • α₀ + η →
          G₁ x ((-τ) • α₀ + η) = G₂ x ((-τ) • α₀ + η)) := by sorry

end Arxiv1611_09952

-- Prove2me | Theorems.Thm_EntropicBarrier_Universal_lemma1_derivatives_logPartition
-- name    : EntropicBarrier.Universal.lemma1_derivatives_logPartition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:25:28.179252+00:00
-- url     : https://prove2.me/theorems/49b438d4-b105-4d56-8389-77dccc609d92
-- title:
--   Lemma 1 (iii) — $\nabla^2 f(\theta)=\Sigma(\theta)$ and $\nabla^3 f(\theta)=T(\theta)$, eqs. (4)–(5)
-- statement:
--   Let $\mathcal K\subset\mathbb R^n$ be a convex body, $f$ its log-Laplace transform and $p_\theta$ its canonical exponential family. For every $\theta\in\mathbb R^n$ and all $h_1,h_2,h_3\in\mathbb R^n$,
--   $$\nabla^2 f(\theta)[h_1,h_2]=\mathbb E_{X\sim p_\theta}\langle X-x(\theta),h_1\rangle\langle X-x(\theta),h_2\rangle=\Sigma(\theta)[h_1,h_2],$$
--   $$\nabla^3 f(\theta)[h_1,h_2,h_3]=\mathbb E_{X\sim p_\theta}\prod_{i=1}^3\langle X-x(\theta),h_i\rangle=T(\theta)[h_1,h_2,h_3].$$
--
--   These are eqs. (4) and (5): the Hessian and third derivative of the log-partition function are the covariance and third central moment of $p_\theta$.
--
--   **Formalization Note** The matrix and tensor identities are stated as equalities of multilinear forms, using `iteratedFDeriv ℝ 2` and `iteratedFDeriv ℝ 3` evaluated at `![h₁, h₂]` and `![h₁, h₂, h₃]`.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 5, Lemma 1 (iii), eqs. (4)-(5)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_EntropicBarrier_Universal_ExpFamily

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

theorem lemma1_derivatives_logPartition {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) (θ : EuclideanSpace ℝ (Fin n)) :
    (∀ h₁ h₂ : EuclideanSpace ℝ (Fin n),
      iteratedFDeriv ℝ 2 (logPartition K) θ ![h₁, h₂] = covForm K θ h₁ h₂) ∧
    (∀ h₁ h₂ h₃ : EuclideanSpace ℝ (Fin n),
      iteratedFDeriv ℝ 3 (logPartition K) θ ![h₁, h₂, h₃] = thirdMomentForm K θ h₁ h₂ h₃) := by sorry

end EntropicBarrier.Universal

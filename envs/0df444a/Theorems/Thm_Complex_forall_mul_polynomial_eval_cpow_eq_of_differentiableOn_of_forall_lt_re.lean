-- Prove2me | Theorems.Thm_Complex_forall_mul_polynomial_eval_cpow_eq_of_differentiableOn_of_forall_lt_re
-- name    : Complex.forall_mul_polynomial_eval_cpow_eq_of_differentiableOn_of_forall_lt_re
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/015ae677-49c6-583b-b7d0-1a52e419281d
-- title:
--   Analytic continuation of a Dirichlet-polynomial identity to a half-plane
-- statement:
--   Let $N$ be a real number with $N>0$, let $\sigma_2,\sigma_0$ be real numbers, and let $f:\mathbb{C}\to\mathbb{C}$ be differentiable (in the complex sense) on the open right half-plane $\{s:\operatorname{Re} s>\sigma_2\}$. Let $P,Q$ be polynomials with complex coefficients. Assume that for every $s$ with $\operatorname{Re} s>\sigma_0$ one has $f(s)\,Q(N^{-s})=P(N^{-s})$, where $N^{-s}$ denotes the complex power of the real number $N$ viewed in $\mathbb{C}$. The conclusion is that the same identity $f(s)\,Q(N^{-s})=P(N^{-s})$ holds for every $s$ with $\operatorname{Re} s>\sigma_2$. No relation between $\sigma_0$ and $\sigma_2$ is assumed: if $\sigma_0<\sigma_2$ the statement is a weakening of the hypothesis, and the content of the theorem is the case $\sigma_0\ge\sigma_2$, in which the identity known only on a smaller half-plane is propagated to the whole half-plane of holomorphy of $f$.
--
--   This is the identity (uniqueness) theorem for holomorphic functions, packaged for identities between a holomorphic function multiplied by a Dirichlet polynomial in $N^{-s}$ and another such polynomial. It is the analytic-continuation step used in the construction of the local Rankin–Selberg integrals for the cubic induction in the Langlands–Tunnell argument, where a functional equation verified in a region of absolute convergence is transported to the full half-plane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_forall_mul_polynomial_eval_cpow_eq_of_differentiableOn_of_forall_lt_re.lean

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Complex.forall_mul_polynomial_eval_cpow_eq_of_differentiableOn_of_forall_lt_re
    (N : ℝ) (hN : 0 < N) (σ₂ σ₀ : ℝ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {s : ℂ | σ₂ < s.re})
    (P Q : Polynomial ℂ)
    (h : ∀ s : ℂ, σ₀ < s.re → f s * Q.eval ((N : ℂ) ^ (-s)) = P.eval ((N : ℂ) ^ (-s))) :
    ∀ s : ℂ, σ₂ < s.re → f s * Q.eval ((N : ℂ) ^ (-s)) = P.eval ((N : ℂ) ^ (-s)) := by sorry

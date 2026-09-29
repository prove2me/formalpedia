-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_archIntertwiningComplex_le_and_norm_deriv_le_of_re_eq_zero
-- name    : AutomorphicForm.exists_forall_norm_archIntertwiningComplex_le_and_norm_deriv_le_of_re_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/bae8ecb5-7628-5ea8-8662-272259a4a09b
-- title:
--   Uniform axis bound for a normalised archimedean Γ-factor
-- statement:
--   Let $a,m,M$ be natural numbers with $2a\le m$, and assume that $m=2a$ forces $M=0$. Define $N:\mathbb C\to\mathbb C$ by $$N(W)=\frac{a!}{2}\cdot\begin{cases}\Gamma(W+1)\,\Gamma(W+1+a)^{-1},& m=2a\ \text{and}\ M=0,\\[1ex] \bigl(W+\tfrac M2\bigr)\,\Gamma\!\bigl(W+\tfrac m2-a\bigr)\,\Gamma\!\bigl(W+\tfrac m2+1\bigr)^{-1},&\text{otherwise},\end{cases}$$ where $a!$, $a$, $m$, $M$ are read as complex numbers and the reciprocals are the inverses in $\mathbb C$ (so they vanish at poles of $\Gamma$, by Lean's convention for division). The assertion is that there exists a real constant $C\ge 0$ — chosen before $W$, hence depending only on $a$, $m$, $M$ — such that for every $W\in\mathbb C$ with $\operatorname{Re}W=0$ one has $\lVert N(W)\rVert\le C$, the function $N$ is complex differentiable at $W$, and $\lVert N'(W)\rVert\le C$. Thus $N$ and its derivative are bounded uniformly on the imaginary axis, and $N$ is holomorphic at each point of that axis.
--
--   The function $N$ is the normalised archimedean intertwining scalar at a complex place, in the variable $W=2s+u$, for the $SU(2)$-type with indices determined by $a$, $m$ and the circle weight $M$; the two branches are rational in $W$ with all shifts having positive real part, which is what makes the bounds on the unitary axis possible. The statement is used in the estimate for the $L^2$-norm of the derivative of the normalised intertwining operator along the axis, [`AutomorphicForm.exists_forall_lintegral_norm_sq_deriv_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat`](thm.html#AutomorphicForm.exists_forall_lintegral_norm_sq_deriv_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_archIntertwiningComplex_le_and_norm_deriv_le_of_re_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.exists_forall_norm_archIntertwiningComplex_le_and_norm_deriv_le_of_re_eq_zero
    (a m M : ℕ) (hm : 2 * a ≤ m) (hM : m = 2 * a → M = 0) :
    let N : ℂ → ℂ := fun W => ((a.factorial : ℕ) : ℂ) / 2 *
      (if m = 2 * a ∧ M = 0 then
        Complex.Gamma (W + 1) * (Complex.Gamma (W + 1 + (a : ℂ)))⁻¹
      else
        (W + (M : ℂ) / 2) * Complex.Gamma (W + (m : ℂ) / 2 - (a : ℂ)) * (Complex.Gamma (W + (m : ℂ) / 2 + 1))⁻¹)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℂ, W.re = 0 → ‖N W‖ ≤ C ∧ DifferentiableAt ℂ N W ∧ ‖deriv N W‖ ≤ C := by sorry

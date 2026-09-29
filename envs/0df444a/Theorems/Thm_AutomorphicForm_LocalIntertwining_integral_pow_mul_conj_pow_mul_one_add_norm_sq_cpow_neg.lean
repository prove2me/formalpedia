-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg
-- name    : AutomorphicForm.LocalIntertwining.integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/3694ef49-5462-5cf1-aafe-af8a36fba7ab
-- title:
--   Beta integral on ℂ for zᵃ̄ z^{ b}(1+|z|²)^{-t}
-- statement:
--   Let $a$ and $b$ be natural numbers and let $t$ be a complex number satisfying $\tfrac{a+b}{2}+1<\operatorname{Re} t$. The assertion concerns the Bochner integral over $\mathbb{C}$, with respect to the standard volume (two-dimensional Lebesgue) measure on $\mathbb{C}$, of the function $z\mapsto z^{a}\,\overline{z}^{\,b}\,(1+\|z\|^{2})^{-t}$, where $\overline{z}$ denotes the image of $z$ under complex conjugation (`starRingEnd ℂ`), the base $1+\|z\|^{2}$ is the real number $1+|z|^{2}$ regarded as a complex number, and the power $(\cdot)^{-t}$ is the complex power of that base. The theorem states that this integral equals $\pi\,a!\,\Gamma(t-1-a)/\Gamma(t)$ when $a=b$, and equals $0$ when $a\neq b$; here $\Gamma$ is the complex Gamma function and $\pi$, $a!$ are coerced into $\mathbb{C}$. The hypothesis on $\operatorname{Re} t$ is the condition for absolute convergence, since the modulus of the integrand is $r^{a+b}(1+r^{2})^{-\operatorname{Re} t}$ with $r=|z|$; it also guarantees $\operatorname{Re}(t-1-a)>0$ in the diagonal case $a=b$, so no pole of $\Gamma$ is met.
--
--   This is the planar Euler Beta integral together with the orthogonality of the circle characters $e^{i(a-b)\theta}$: it evaluates the moments of the weight $(1+|z|^{2})^{-t}$ against monomials $z^{a}\bar z^{\,b}$. It supplies the archimedean computation at a complex place underlying the meromorphic continuation and growth estimates for the normalised intertwining operator on $K$-finite sections, and is used by the statements producing analytic continuation of `normalisedIntertwining` and the associated $L^{2}$ bounds; the base case $\int_{\mathbb{C}}(1+\|z\|^{2})^{-(2s+1)}=\pi/(2s)$ for $\operatorname{Re} s>0$ is [`AutomorphicForm.LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div`](thm.html#AutomorphicForm.LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.LocalIntertwining.integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg
    (a b : ℕ) (t : ℂ) (ht : ((a : ℝ) + b) / 2 + 1 < t.re) :
    ∫ z : ℂ, z ^ a * (starRingEnd ℂ z) ^ b * ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-t)
      = if a = b then (Real.pi : ℂ) * (a.factorial : ℂ) * Complex.Gamma (t - 1 - a) / Complex.Gamma t
        else 0 := by sorry

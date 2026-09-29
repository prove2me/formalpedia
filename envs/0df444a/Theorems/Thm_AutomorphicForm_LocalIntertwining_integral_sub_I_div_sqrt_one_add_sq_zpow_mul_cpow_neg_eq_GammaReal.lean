-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal
-- name    : AutomorphicForm.LocalIntertwining.integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/c684fd69-e085-55fe-80a5-f82becf7526f
-- title:
--   Weight-k archimedean intertwining integral as a Γ_ℝ-quotient
-- statement:
--   For an integer $k$ and a complex number $s$ with $\operatorname{Re} s>0$, the Bochner integral over $\mathbb R$, against Lebesgue measure, of the function $$x\longmapsto \Bigl(\frac{x-i}{\sqrt{1+x^{2}}}\Bigr)^{k}\,(1+x^{2})^{-(s+1/2)}$$ equals $$(-i)^{k}\,\frac{\Gamma_{\mathbb R}(2s)\,\Gamma_{\mathbb R}(2s+1)}{\Gamma_{\mathbb R}(2s+1+k)\,\Gamma_{\mathbb R}(2s+1-k)}.$$ Here the first factor is the $k$-th integer power (so a reciprocal power when $k<0$) of the complex number $(x-i)/\sqrt{1+x^{2}}$, whose modulus is $1$; the real square root $\sqrt{1+x^{2}}$ and the real number $1+x^{2}$ are coerced into $\mathbb C$, and $(1+x^{2})^{-(s+1/2)}$ is the principal-branch complex power of the positive real base. On the right, $\Gamma_{\mathbb R}$ is Mathlib's real archimedean Gamma factor $\Gamma_{\mathbb R}(w)=\pi^{-w/2}\,\Gamma(w/2)$, with $\Gamma$ taking the value $0$ at its poles and with division by $0$ giving $0$; thus at the points of the half-plane where $2s+1+k$ or $2s+1-k$ is a pole of $\Gamma_{\mathbb R}$ the right-hand side is read as $0$, and the assertion includes that the integral vanishes there. The argument $k$ is coerced from $\mathbb Z$ to $\mathbb C$ in the Gamma arguments.
--
--   This is the weight-$k$ companion of Euler's integral $\int_{\mathbb R}(1+x^{2})^{-a}\,dx=\sqrt{\pi}\,\Gamma(a-\tfrac12)/\Gamma(a)$, the spherical case $k=0$ being the cited identity [`AutomorphicForm.LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div`](thm.html#AutomorphicForm.LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div); it computes the archimedean local factor by which the standard intertwining integral for a principal series of $\mathrm{GL}_2(\mathbb R)$ acts on the vector of $\mathrm{O}(2)$-weight $k$. It feeds the construction and analytic continuation of normalised intertwining operators for the automorphic forms part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal.lean

import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.LocalIntertwining.integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal
    (k : ℤ) (s : ℂ) (hs : 0 < s.re) :
    ∫ x : ℝ, (((x : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
        * ((1 + x ^ 2 : ℝ) : ℂ) ^ (-(s + 1 / 2))
      = (-Complex.I) ^ k * (Complex.Gammaℝ (2 * s) * Complex.Gammaℝ (2 * s + 1))
          / (Complex.Gammaℝ (2 * s + 1 + k) * Complex.Gammaℝ (2 * s + 1 - k)) := by sorry

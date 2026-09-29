-- Prove2me | Theorems.Thm_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay
-- name    : AutomorphicForm.RealIwasawa.norm_fourierIntegral_cpow_rad_mul_le_polyDecay
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/eca6c263-6d71-5d97-93bd-b3b39acaae5b
-- title:
--   Rapid decay of the Fourier integral of r_g^{-u}P
-- statement:
--   Let $g$ be a $2\times 2$ real matrix with $\det g\neq 0$, let $u\in\mathbb{C}$ satisfy $\operatorname{Re}u>1$, and let $P:\mathbb{R}\to\mathbb{C}$ be infinitely differentiable with all derivatives bounded: for each $n\in\mathbb{N}$ there is $C>0$ with $\|D^nP(x)\|\le C$ for all $x\in\mathbb{R}$. Let $L:\mathbb{R}\to\mathbb{R}\to\mathbb{R}$ be a continuous bilinear form, let $c>0$, and assume that $L$ is coercive in its second variable with constant $c$, in the sense that for every $\xi\in\mathbb{R}$ there is $v$ with $\|v\|\le 1$ and $c\|\xi\|\le\|L\,v\,\xi\|$. Let $N\in\mathbb{N}$. Then there is a constant $C>0$ such that for every $\xi\in\mathbb{R}$,
--   $$\Bigl\|\int_{\mathbb{R}} \mathbf{e}(-L(x,\xi))\,\bigl(\sqrt{(g_{00}+x g_{10})^2+(g_{01}+x g_{11})^2}\bigr)^{-u} P(x)\,dx\Bigr\|\le C\,(1+\|\xi\|)^{-N},$$
--   where the integral is the Fourier integral with respect to Lebesgue measure, the standard additive character $\mathbf{e}$ and the pairing induced by $L$, the base of the complex power is the indicated nonnegative real number viewed in $\mathbb{C}$, and the decay exponent $-(N:\mathbb{R})$ is a real power.
--
--   This is the real-place non-stationary-phase estimate for an archimedean factor: the weight is the Iwasawa radial length of the lower row of $w\,n(x)\,g$ raised to a complex power, $P$ carries the $K$-type, and the conclusion is decay of arbitrary polynomial order in the frequency variable. It is used by [`AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary`](thm.html#AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary) to majorise unipotent-averaged kernels built from $K$-finite vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RealIwasawa_norm_fourierIntegral_cpow_rad_mul_le_polyDecay.lean

import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped ContDiff FourierTransform

theorem AutomorphicForm.RealIwasawa.norm_fourierIntegral_cpow_rad_mul_le_polyDecay
    {g : Matrix (Fin 2) (Fin 2) ℝ} (hg : g.det ≠ 0) {u : ℂ} (hu : 1 < u.re)
    {P : ℝ → ℂ} (hPC : ContDiff ℝ ∞ P)
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ n P x‖ ≤ C)
    (L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℝ, ∃ v : ℝ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun x => ((Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2) : ℂ) ^ (-u)) * P x) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by sorry

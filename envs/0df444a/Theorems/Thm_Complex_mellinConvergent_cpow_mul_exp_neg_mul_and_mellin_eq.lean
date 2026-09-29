-- Prove2me | Theorems.Thm_Complex_mellinConvergent_cpow_mul_exp_neg_mul_and_mellin_eq
-- name    : Complex.mellinConvergent_cpow_mul_exp_neg_mul_and_mellin_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/4fb31ca6-8692-5c23-a187-f259622a45fe
-- title:
--   Mellin transform of t^ke^{-rt} equals r^{-(s+k)}Γ(s+k)
-- statement:
--   Let $k$ and $r$ be real numbers with $r>0$, and let $s$ be a complex number whose real part satisfies $\operatorname{Re}(s)>-k$. Consider the function $f:\mathbb{R}\to\mathbb{C}$ given by $f(t)=t^{k}e^{-rt}$, formed using the complex power $(t:\mathbb{C})^{(k:\mathbb{C})}$ of the real number $t$ coerced to $\mathbb{C}$ and `Complex.exp` of $-(rt)$. The theorem asserts two things simultaneously. First, `MellinConvergent f s` holds: the function $t\mapsto t^{s-1}\cdot f(t)$ is integrable on the open half-line $(0,\infty)$ for Lebesgue measure. Second, the value of the Mellin transform is computed: $$\mathrm{mellin}(f)(s)=\int_0^{\infty}t^{s-1}t^{k}e^{-rt}\,dt=\left(\tfrac{1}{r}\right)^{s+k}\Gamma(s+k),$$ where the power on the right is the complex power of $1/r$ with exponent $s+k$ and $\Gamma$ is `Complex.Gamma`. Both assertions use only Mathlib notions; no project-specific definitions occur. Note that the hypothesis $\operatorname{Re}(s)>-k$ is exactly the condition $\operatorname{Re}(s+k)>0$ under which the Euler integral converges.
--
--   This is the classical Euler $\Gamma$-integral $\int_0^{\infty}t^{z-1}e^{-rt}\,dt=r^{-z}\Gamma(z)$ for $\operatorname{Re}(z)>0$ and $r>0$, packaged as a statement about Mellin convergence and the Mellin transform at $z=s+k$. It supplies the archimedean local computation used downstream: with weight parameter $k$ and $r=4\pi$ it evaluates the integral $\int_0^{\infty}\lvert y^{k/2}e^{-2\pi y}\rvert^{2}y^{s-1}\,dy$ attached to the lowest-weight vector of a holomorphic discrete series, and it is invoked in the Rankin–Selberg and cubic-induction parts of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_mellinConvergent_cpow_mul_exp_neg_mul_and_mellin_eq.lean

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Complex.mellinConvergent_cpow_mul_exp_neg_mul_and_mellin_eq
    (k r : ℝ) (hr : 0 < r) (s : ℂ) (hs : -k < s.re) :
    MellinConvergent (fun t : ℝ => ((t : ℂ) ^ (k : ℂ)) * Complex.exp (-((r : ℂ) * (t : ℂ)))) s ∧
    mellin (fun t : ℝ => ((t : ℂ) ^ (k : ℂ)) * Complex.exp (-((r : ℂ) * (t : ℂ)))) s =
      (1 / (r : ℂ)) ^ (s + (k : ℂ)) * Complex.Gamma (s + (k : ℂ)) := by sorry

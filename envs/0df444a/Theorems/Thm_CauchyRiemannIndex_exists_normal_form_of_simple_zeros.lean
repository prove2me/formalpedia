-- Prove2me | Theorems.Thm_CauchyRiemannIndex_exists_normal_form_of_simple_zeros
-- name    : CauchyRiemannIndex.exists_normal_form_of_simple_zeros
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T14:06:56.156411+00:00
-- url     : https://prove2.me/theorems/f1220378-9062-4aba-8f19-dac160ee1f56
-- title:
--   Putting evenly spaced simple zeros of a periodic function on the cylinder into the normal form z or z̄
-- statement:
--   Let $N\ge1$ and $t_m=(m+\tfrac12)/N$ for $m=0,\dots,N-1$. Let $f:\mathbb{R}\times\mathbb{R}\to\mathbb{C}$ be smooth and $1$-periodic in the second variable, with $f(0,t_m)=0$ for every $m$. Suppose that at each of these points the derivative has the form
--   $$df_{(0,t_m)}(x,y)=c_m\,L(x,y),\qquad c_m\in\mathbb{C}\setminus\{0\},$$
--   where either $L(x,y)=x+iy$ for all $m$, or $L(x,y)=x-iy$ for all $m$. Then there are $r\in(0,\tfrac1{20}]$ and a smooth function $\beta:\mathbb{R}\times\mathbb{R}\to\mathbb{C}$, $1$-periodic in the second variable, such that
--
--   1. $\beta(s,t)=f(s,t)$ whenever $|s|\ge\tfrac12$;
--   2. $\beta$ and $f$ have the same zeros: $\beta(x)=0\iff f(x)=0$;
--   3. for every $m$ and every $z\in\mathbb{C}$ with $|z|<r$,
--   $$\beta\bigl((0,t_m)+(\operatorname{Re}z,\operatorname{Im}z)\bigr)=\begin{cases}z,&L(x,y)=x+iy,\\ \bar z,&L(x,y)=x-iy.\end{cases}$$
--
--   This replaces a function on the cylinder whose zeros are simple, of one orientation, and evenly spaced on the circle $\{0\}\times S^1$, by one with the same zero set that is exactly $z$ or $\bar z$ near each zero, which is the normal form required of antilinear perturbation terms for Cauchy–Riemann operators.
--
--   **Formalization Note** The flag `cj : Bool` selects $L$: `false` gives `Complex.equivRealProdCLM.symm` ($(x,y)\mapsto x+iy$), `true` gives its composition with complex conjugation. The derivative hypothesis is `HasFDerivAt f (c m • L) (0, t_m)`, the normal form is stated as `β (0 + z.re, t_m + z.im) = if cj then starRingEnd ℂ z else z`, and smoothness is `ContDiff ℝ ∞`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, §5.8, pp. 102-103

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace CauchyRiemannIndex

open scoped ContDiff

/-- Let `f : ℝ × S¹ → ℂ` be smooth and `1`-periodic in `t`, vanishing at the `N` points
`ζ_m = (0, (m + 1/2)/N)`, where its derivative is `c_m L` with `c_m ≠ 0` and `L(x, y) = x + iy`
(or `L(x, y) = x - iy` for all `m` when `cj = true`). Then there are `r ∈ (0, 1/20]` and a smooth
`t`-periodic `β` with the same zero set as `f`, equal to `f` for `|s| ≥ 1/2`, and with
`β(ζ_m + z) = z` (resp. `z̄`) for `|z| < r`. -/
theorem exists_normal_form_of_simple_zeros (N : ℕ) (hN : 0 < N) (cj : Bool) (f : ℝ × ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hper : ∀ s t, f (s, t + 1) = f (s, t))
    (hzero : ∀ m : Fin N, f (0, ((m : ℝ) + 1 / 2) / N) = 0)
    (c : Fin N → ℂ) (hc : ∀ m, c m ≠ 0)
    (hD : ∀ m : Fin N, HasFDerivAt f (c m • (if cj then
        (Complex.conjCLE.toContinuousLinearMap).comp
          Complex.equivRealProdCLM.symm.toContinuousLinearMap
      else Complex.equivRealProdCLM.symm.toContinuousLinearMap)) (0, ((m : ℝ) + 1 / 2) / N)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 20 ∧ ∃ β : ℝ × ℝ → ℂ, ContDiff ℝ ∞ β ∧
      (∀ s t, β (s, t + 1) = β (s, t)) ∧
      (∀ x : ℝ × ℝ, 1 / 2 ≤ |x.1| → β x = f x) ∧ (∀ x, β x = 0 ↔ f x = 0) ∧
      ∀ m : Fin N, ∀ z : ℂ, ‖z‖ < r →
        β (0 + z.re, ((m : ℝ) + 1 / 2) / N + z.im) = if cj then (starRingEnd ℂ) z else z := by
  sorry

end CauchyRiemannIndex

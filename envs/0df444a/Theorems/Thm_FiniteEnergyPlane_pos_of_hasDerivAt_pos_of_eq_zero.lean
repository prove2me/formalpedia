-- Prove2me | Theorems.Thm_FiniteEnergyPlane_pos_of_hasDerivAt_pos_of_eq_zero
-- name    : FiniteEnergyPlane.pos_of_hasDerivAt_pos_of_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T21:48:34.620448+00:00
-- url     : https://prove2.me/theorems/6a3447c1-2bfb-4583-ac93-056b2eb4fc1c
-- title:
--   A function vanishing at the left endpoint whose zeros are upward crossings is positive at the right endpoint
-- statement:
--   Let $a<b$ and let $f:\mathbb{R}\to\mathbb{R}$ be differentiable at every point of $[a,b]$, with derivative $f'(t)$ at $t$. Suppose $f(a)=0$ and $f'(t)>0$ at every $t\in[a,b]$ with $f(t)=0$. Then $f(b)>0$.
--
--   An elementary one-variable fact for real functions whose zeros are all strict upward crossings; it is used to control the sign of cross terms of solutions of linear ODEs.
--
--   **Formalization Note** Differentiability is `∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t` for a given function `f'`; the conclusion is `0 < f b`.
-- source:
--   Standard real analysis; used in C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7.

import Mathlib.Analysis.Calculus.Deriv.Basic

namespace FiniteEnergyPlane

/-- Let `a < b` and let `f : ℝ → ℝ` have derivative `f' t` at every `t ∈ [a, b]`. If `f a = 0`
and `f' t > 0` at every zero `t ∈ [a, b]` of `f`, then `f b > 0`. -/
theorem pos_of_hasDerivAt_pos_of_eq_zero {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t) (ha : f a = 0)
    (hz : ∀ t ∈ Set.Icc a b, f t = 0 → 0 < f' t) : 0 < f b := by
  sorry

end FiniteEnergyPlane

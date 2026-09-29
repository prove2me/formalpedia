-- Prove2me | Theorems.Thm_Complex_exists_forall_ne_zero_re_gt_of_differentiableOn_of_exists_ne_zero
-- name    : Complex.exists_forall_ne_zero_re_gt_of_differentiableOn_of_exists_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/22ba16c4-9c6e-5a8a-a5d1-99c96cc30e78
-- title:
--   Simultaneous non-vanishing far right in a half-plane
-- statement:
--   Let $\iota$ be a type, $t$ a finite subset of $\iota$, $f : \iota \to \mathbb{C} \to \mathbb{C}$ a family of functions and $\sigma$ a real number. Assume that for each $i \in t$ the function $f_i$ is differentiable (in the complex sense) on the open half-plane $\{s \in \mathbb{C} : \sigma < \Re s\}$, and that for each $i \in t$ there is at least one point $s$ with $\sigma < \Re s$ at which $f_i(s) \neq 0$. Then for every real $\sigma'$ there exists a point $s \in \mathbb{C}$ with $\sigma' < \Re s$ and $\sigma < \Re s$ such that $f_i(s) \neq 0$ for all $i \in t$. Thus the non-vanishing is simultaneous over the whole finite family, and the point can be taken with real part as large as desired; the conclusion records both inequalities $\sigma' < \Re s$ and $\sigma < \Re s$ separately, so that membership in the domain of holomorphy is available without comparing $\sigma$ and $\sigma'$.
--
--   This is the standard consequence of the identity theorem that finitely many functions holomorphic on a right half-plane, none of them identically zero there, have a common non-zero point arbitrarily far to the right. It is used in the Rankin–Selberg part of the Langlands–Tunnell input, to choose a point at which a finite family of archimedean integrals attached to pure translates is simultaneously non-zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_exists_forall_ne_zero_re_gt_of_differentiableOn_of_exists_ne_zero.lean

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Complex.exists_forall_ne_zero_re_gt_of_differentiableOn_of_exists_ne_zero
    {ι : Type} (t : Finset ι) (f : ι → ℂ → ℂ) (σ : ℝ)
    (hf : ∀ i ∈ t, DifferentiableOn ℂ (f i) {s : ℂ | σ < s.re})
    (hne : ∀ i ∈ t, ∃ s : ℂ, σ < s.re ∧ f i s ≠ 0)
    (σ' : ℝ) :
    ∃ s : ℂ, σ' < s.re ∧ σ < s.re ∧ ∀ i ∈ t, f i s ≠ 0 := by sorry

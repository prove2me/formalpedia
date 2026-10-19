-- Prove2me | Theorems.Thm_CauchyRiemannIndex_arg_add_one_sub_eq
-- name    : CauchyRiemannIndex.arg_add_one_sub_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T16:37:07.778062+00:00
-- url     : https://prove2.me/theorems/2e1a94d5-6222-4838-a6e3-c1e7796c6767
-- title:
--   A continuous argument of a periodic nonvanishing loop increases by the same multiple of 2π over every period
-- statement:
--   Let $\beta:\mathbb{R}\to\mathbb{C}\setminus\{0\}$ be $1$-periodic and let $\theta:\mathbb{R}\to\mathbb{R}$ be a continuous argument of $\beta$, i.e. $\beta(t)=|\beta(t)|\,e^{i\theta(t)}$ for all $t$. If $\theta(1)-\theta(0)=2\pi w$ with $w\in\mathbb{Z}$, then $\theta(t+1)-\theta(t)=2\pi w$ for every $t\in\mathbb{R}$.
--
--   Equivalently, $t\mapsto\theta(t)-2\pi w t$ is $1$-periodic, so the winding number of a loop $S^1\to\mathbb{C}\setminus\{0\}$ can be read off from any period of a continuous argument.
--
--   **Formalization Note** The loop is a function on $\mathbb{R}$ with `Function.Periodic β 1`; the argument is only assumed continuous on $\mathbb{R}$ (no periodicity).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, §5.8, pp. 102-103

import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace CauchyRiemannIndex

/-- If `θ` is a continuous argument of a nowhere-vanishing `1`-periodic loop `β`
(`β = |β| e^{iθ}`) and `θ(1) - θ(0) = 2πw`, then `θ(t + 1) - θ(t) = 2πw` for every `t`. -/
theorem arg_add_one_sub_eq (β : ℝ → ℂ) (hper : Function.Periodic β 1) (hnz : ∀ t, β t ≠ 0)
    (θ : ℝ → ℝ) (hθ : Continuous θ)
    (harg : ∀ t, β t = ‖β t‖ * Complex.exp (θ t * Complex.I))
    (w : ℤ) (hw : θ 1 - θ 0 = 2 * Real.pi * w) (t : ℝ) :
    θ (t + 1) - θ t = 2 * Real.pi * w := by
  sorry

end CauchyRiemannIndex

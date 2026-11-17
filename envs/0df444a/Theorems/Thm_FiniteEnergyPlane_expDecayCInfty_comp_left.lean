-- Prove2me | Theorems.Thm_FiniteEnergyPlane_expDecayCInfty_comp_left
-- name    : FiniteEnergyPlane.expDecayCInfty_comp_left
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T21:43:49.481861+00:00
-- url     : https://prove2.me/theorems/3ac751d0-2ec4-4564-85d5-c3fa6fa3dcdd
-- title:
--   Exponential C-infinity decay on an end is preserved by smooth maps vanishing at zero
-- statement:
--   Let $E$ be a finite-dimensional real normed space and $F$ a real normed space. Let $a : \mathbb{R}\times\mathbb{R} \to E$ decay like $e^{-bs}$ in $C^\infty$ on the end $s \to +\infty$, with $b > 0$: $a$ is smooth on some $(s_0, \infty) \times \mathbb{R}$, and for every $m$ there are $C, s_1$ with $\|D^m a(s,t)\| \le C e^{-bs}$ for $s \ge s_1$ and all $t$. Let $G : E \to F$ be smooth on the ball of radius $r > 0$ about $0$ with $G(0) = 0$. Then $G \circ a$ decays like $e^{-bs}$ in $C^\infty$.
--
--   Role: lets exponential asymptotics be pushed through smooth nonlinear operations (logarithms, inverses, normalizations) on a cylindrical end.
--
--   Formalization Note: decay is `ExpDecayCInfty a b`.
-- source:
--   Standard calculus of exponential decay on cylindrical ends; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff Real

/-- Exponential `C^∞` decay on a cylindrical end is preserved under composition on the left with a
map that is smooth near `0` and vanishes at `0`: if `a` decays like `e^{-bs}` (`b > 0`) and `G` is
smooth on `ball 0 r` with `G 0 = 0`, then `G ∘ a` decays like `e^{-bs}`. -/
theorem expDecayCInfty_comp_left {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : E → F) (r : ℝ) (hr : 0 < r) (hG : ContDiffOn ℝ ∞ G (ball 0 r)) (hG0 : G 0 = 0)
    (a : ℝ × ℝ → E) (b : ℝ) (hb : 0 < b) (ha : ExpDecayCInfty a b) :
    ExpDecayCInfty (fun p => G (a p)) b := by
  sorry

end FiniteEnergyPlane

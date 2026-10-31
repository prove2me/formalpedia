-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_period_near_of_forall_shift_close
-- name    : FiniteEnergyPlane.exists_period_near_of_forall_shift_close
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-30T14:48:40.928093+00:00
-- url     : https://prove2.me/theorems/ffa22c1c-f39a-4d7c-b585-74d2c4157f00
-- title:
--   Shifts that nearly fix a periodic map are close to exact periods
-- statement:
--   Let $E$ be a normed group, $T>0$, and $x:\mathbb{R}\to E$ continuous and $T$-periodic. Then for every $\delta>0$ there is $\eta>0$ with the following property: if $a\in\mathbb{R}$ satisfies $\|x(y+a)-x(y)\|\le\eta$ for all $y\in\mathbb{R}$, then there is an exact period $p$ of $x$ (that is, $x(y+p)=x(y)$ for all $y$) with $|a-p|<\delta$.
--
--   So a shift that moves $x$ uniformly very little is close to a symmetry of $x$. Here $T$ need not be the minimal period, and $x$ may be constant. The statement is used to compare phases $c,c'$ for which $x(\cdot+c)$ and $x(\cdot+c')$ are uniformly close, for instance phases of a periodic orbit that may be a multiple cover.
--
--   **Formalization Note** Exact periods are the reals $p$ with `∀ y, x (y + p) = x y`; the conclusion gives one such $p$ with `|a - p| < δ`.
-- source:
--   Used for H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics (1996), Theorem 1.3

import Mathlib

namespace FiniteEnergyPlane

open Filter Topology

/-- Let `x : ℝ → E` be continuous and `T`-periodic. For every `δ > 0` there is `η > 0` such that
whenever the shift `x(· + a)` is uniformly `η`-close to `x`, the number `a` lies within `δ` of an
exact period `p` of `x` (`x(y + p) = x(y)` for all `y`). -/
theorem exists_period_near_of_forall_shift_close {E : Type*} [NormedAddCommGroup E]
    {x : ℝ → E} {T : ℝ} (hT : 0 < T) (hx : Continuous x) (hxT : Function.Periodic x T)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ η > 0, ∀ a : ℝ, (∀ y : ℝ, ‖x (y + a) - x y‖ ≤ η) →
      ∃ p : ℝ, (∀ y : ℝ, x (y + p) = x y) ∧ |a - p| < δ := by
  sorry

end FiniteEnergyPlane

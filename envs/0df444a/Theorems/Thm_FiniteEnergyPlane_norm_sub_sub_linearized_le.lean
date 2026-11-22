-- Prove2me | Theorems.Thm_FiniteEnergyPlane_norm_sub_sub_linearized_le
-- name    : FiniteEnergyPlane.norm_sub_sub_linearized_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T15:49:01.07872+00:00
-- url     : https://prove2.me/theorems/eccc46d0-dcad-4393-8db9-d6c17aeaae7d
-- title:
--   A trajectory near a reference trajectory is quadratically close to the linearized solution
-- statement:
--   Let $E$ be a real normed space and $R : E \to E$ a vector field. Let $x$ and $y$ be trajectories of $R$ on $\mathbb{R}$ ($x' = R(x)$, $y' = R(y)$), let $c \in \mathbb{R}$, and let $v$ solve the linearized equation $v'(t) = DR(x(c + t))\,v(t)$. Let $\delta, D, L, M$ be constants with $D, L \ge 0$, and suppose:
--   - on every ball $\bar B(x(t), \delta)$ the field $R$ is $D$-Lipschitz and satisfies $\|R(z) - R(x(t)) - DR(x(t))(z - x(t))\| \le D\,\|z - x(t)\|^2$;
--   - $\|v(t)\| \le M \le \delta$ for $t \in [-L, L]$;
--   - $\|y(0) - x(c)\|\,e^{DL} < \delta$.
--
--   Then for all $t \in [-L, L]$:
--   $$\|y(t) - x(c + t)\| \le \|y(0) - x(c)\|\,e^{DL}, \qquad \|y(t) - x(c + t) - v(t)\| \le \big(\|y(0) - x(c) - v(0)\| + D M^2 L\big)\,e^{(D+1)L}.$$
--
--   Role: over a fixed time window, a trajectory starting near a reference trajectory follows the linearized solution up to an error quadratic in the size of the perturbation, in both time directions.
--
--   Formalization Note: trajectories are `∀ t, HasDerivAt x (R (x t)) t`; $DR(p)$ is `fderiv ℝ R p`.
-- source:
--   Standard (Grönwall's inequality); used for U. Hryniewicz, Trans. AMS 364 (2012), proof of Lemma 6.9

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace FiniteEnergyPlane

open Metric Set

/-- Quadratic closeness to the linearization along a trajectory. Let `x` and `y` be trajectories
of a vector field `R` on a real normed space, and let `v` solve the linearized equation
`v'(t) = DR(x(c + t)) v(t)`. Suppose that on every ball `closedBall (x t) δ` the field `R` is
`D`-Lipschitz and satisfies `‖R z - R(x t) - DR(x t)(z - x t)‖ ≤ D ‖z - x t‖²`, that
`‖v‖ ≤ M ≤ δ` on `[-L, L]`, and that `‖y 0 - x c‖ e^{DL} < δ`. Then for `t ∈ [-L, L]`,
`‖y t - x(c + t)‖ ≤ ‖y 0 - x c‖ e^{DL}` and
`‖y t - x(c + t) - v t‖ ≤ (‖y 0 - x c - v 0‖ + D M² L) e^{(D+1)L}`. -/
theorem norm_sub_sub_linearized_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : E → E} {x y v : ℝ → E} {δ D L M c : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hlip : ∀ t, ∀ z ∈ closedBall (x t) δ, ∀ z' ∈ closedBall (x t) δ,
      ‖R z - R z'‖ ≤ D * ‖z - z'‖)
    (hquad : ∀ t, ∀ z ∈ closedBall (x t) δ,
      ‖R z - R (x t) - fderiv ℝ R (x t) (z - x t)‖ ≤ D * ‖z - x t‖ ^ 2)
    (hx : ∀ t, HasDerivAt x (R (x t)) t) (hy : ∀ t, HasDerivAt y (R (y t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ R (x (c + t)) (v t)) t)
    (hvM : ∀ t ∈ Icc (-L) L, ‖v t‖ ≤ M) (hMδ : M ≤ δ)
    (hy0 : ‖y 0 - x c‖ * Real.exp (D * L) < δ) :
    ∀ t ∈ Icc (-L) L, ‖y t - x (c + t)‖ ≤ ‖y 0 - x c‖ * Real.exp (D * L) ∧
      ‖y t - x (c + t) - v t‖ ≤
        (‖y 0 - x c - v 0‖ + D * M ^ 2 * L) * Real.exp ((D + 1) * L) := by
  sorry

end FiniteEnergyPlane

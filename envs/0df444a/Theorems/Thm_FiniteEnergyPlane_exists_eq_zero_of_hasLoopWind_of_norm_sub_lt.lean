-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_eq_zero_of_hasLoopWind_of_norm_sub_lt
-- name    : FiniteEnergyPlane.exists_eq_zero_of_hasLoopWind_of_norm_sub_lt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-05T20:20:51.108781+00:00
-- url     : https://prove2.me/theorems/4315d65f-76c4-414d-94ae-57f51b178459
-- title:
--   A function close to one with nonzero boundary winding has a zero in the disc
-- statement:
--   Let $c\in\mathbb{C}$, $R>0$, and $g,h:\mathbb{C}\to\mathbb{C}$. Suppose $g$ is continuous on $\bar B(c,R)$, the loop $t\mapsto h(c+Re^{2\pi i t})$ lies in $\mathbb{C}\setminus\{0\}$ with winding number $k\neq 0$, and $|g-h|<|h|$ on the circle $|z-c|=R$. Then $g$ has a zero in $\bar B(c,R)$.
--
--   Role: a topological existence principle for zeros of continuous functions, with no differentiability of $g$ assumed.
-- source:
--   Standard Rouché-type statement for continuous functions in the plane

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Metric

/-- Let `h` have nonzero winding number along the circle of radius `R` about `c`, and let `g` be
continuous on the closed disc with `‖g - h‖ < ‖h‖` on that circle. Then `g` has a zero in the
closed disc. -/
theorem exists_eq_zero_of_hasLoopWind_of_norm_sub_lt (g h : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hg : ContinuousOn g (closedBall c R)) (k : ℤ) (hk : k ≠ 0)
    (hw : HasLoopWind (fun t => h (c + ccwLoop R t)) k)
    (hclose : ∀ t : ℝ, ‖g (c + ccwLoop R t) - h (c + ccwLoop R t)‖ < ‖h (c + ccwLoop R t)‖) :
    ∃ z ∈ closedBall c R, g z = 0 := by
  sorry

end FiniteEnergyPlane

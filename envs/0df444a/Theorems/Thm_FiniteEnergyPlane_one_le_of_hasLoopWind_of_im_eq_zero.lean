-- Prove2me | Theorems.Thm_FiniteEnergyPlane_one_le_of_hasLoopWind_of_im_eq_zero
-- name    : FiniteEnergyPlane.one_le_of_hasLoopWind_of_im_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T21:19:24.889482+00:00
-- url     : https://prove2.me/theorems/8ac7d502-0769-4746-9c56-b638702bc8c3
-- title:
--   A loop whose imaginary part has derivative a positive multiple of its real part, and which is somewhere real, winds at least once
-- statement:
--   Let $g:\mathbb{R}\to\mathbb{C}\setminus\{0\}$ be a continuous $1$-periodic loop with winding number $k\in\mathbb{Z}$, and let $c>0$ be a constant such that $t\mapsto\operatorname{Im}g(t)$ is differentiable with
--   $$\frac{d}{dt}\operatorname{Im}g(t)=c\,\operatorname{Re}g(t)\qquad\text{for all }t\in\mathbb{R}.$$
--   If $\operatorname{Im}g(t_0)=0$ for some $t_0\in\mathbb{R}$, then $k\ge 1$.
--
--   A sharpening of the statement that such loops have nonnegative winding, for loops that meet the real axis. It applies to the cross term $\overline{f_1}f_2$ of two eigenfunctions of the asymptotic operator $-J_0\partial_t-S_\infty$ with distinct eigenvalues.
--
--   **Formalization Note** The winding hypothesis is `HasLoopWind g k` (`FiniteEnergyPlane_Winding`: continuous, $1$-periodic, nowhere zero, with a continuous argument $\theta$, $g=|g|e^{i\theta}$, $\theta(1)-\theta(0)=2\pi k$); the derivative hypothesis is a `HasDerivAt` statement for `fun s => (g s).im` at every `t`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7; H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Section 3.

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- A loop in `ℂ \ {0}` whose imaginary part has derivative `c` times its real part, for a
constant `c > 0`, and which is real at some time `t₀`, has winding number at least `1`. -/
theorem one_le_of_hasLoopWind_of_im_eq_zero {g : ℝ → ℂ} {k : ℤ} {c : ℝ}
    (hg : HasLoopWind g k) (hc : 0 < c)
    (hd : ∀ t, HasDerivAt (fun s => (g s).im) (c * (g t).re) t) {t₀ : ℝ}
    (ht₀ : (g t₀).im = 0) : 1 ≤ k := by
  sorry

end FiniteEnergyPlane

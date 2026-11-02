-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasLoopWind_nonneg_of_hasDerivAt_im
-- name    : FiniteEnergyPlane.hasLoopWind_nonneg_of_hasDerivAt_im
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T20:53:25.181546+00:00
-- url     : https://prove2.me/theorems/c6a1017a-9b45-42f9-bd2f-444ca96eef60
-- title:
--   Loops whose imaginary part has derivative a positive multiple of the real part have nonnegative winding
-- statement:
--   Let $g:\mathbb{R}\to\mathbb{C}$ be a continuous $1$-periodic nowhere-zero loop with winding number $k$. Suppose that for some constant $c>0$ the imaginary part of $g$ is differentiable on $\mathbb{R}$ with $(\operatorname{Im} g)'(t)=c\,\operatorname{Re} g(t)$ for all $t$. Then $k\ge 0$.
--
--   A sign criterion for winding numbers of loops in $\mathbb{C}\setminus\{0\}$, used to compare windings of eigenfunctions of asymptotic operators.
--
--   **Formalization Note** The hypotheses are `HasLoopWind g k` (from `FiniteEnergyPlane_Winding`), `0 < c` and `HasDerivAt (fun s => (g s).im) (c * (g t).re) t` for every `t`; the conclusion is `0 ≤ k`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory (2026 notes), arXiv:1612.01009, Section 3.7; H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Section 3.

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

/-- A loop in `ℂ \ {0}` whose imaginary part has derivative `c` times its real part, for a
constant `c > 0`, has nonnegative winding number. -/
theorem hasLoopWind_nonneg_of_hasDerivAt_im {g : ℝ → ℂ} {k : ℤ} {c : ℝ}
    (hg : HasLoopWind g k) (hc : 0 < c)
    (hd : ∀ t, HasDerivAt (fun s => (g s).im) (c * (g t).re) t) : 0 ≤ k := by
  sorry

end FiniteEnergyPlane

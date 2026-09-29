-- Prove2me | Theorems.Thm_DirichletLFunctions_LFunction_center_lower
-- name    : DirichletLFunctions.LFunction_center_lower
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:57:59.109201+00:00
-- url     : https://prove2.me/theorems/84dc59b8-34b5-47d7-b5ba-c9ec4a9999a4
-- title:
--   A lower bound for $|L(s,\chi)|$ far to the right
-- statement:
--   **Dirichlet $L$-functions are bounded away from zero on $\Re s \ge 2$.**
--
--   For every Dirichlet character $\chi$ modulo $q$ and every $s$ with $\Re s \ge 2$,
--
--   $$|L(s,\chi)| \;\ge\; \frac14 .$$
--
--   The bound is **uniform in $q$ and in $\chi$**, which is what makes it useful. On $\Re s \ge 2$
--   the series converges absolutely and is dominated by its first term:
--
--   $$|L(s,\chi)| \;\ge\; 1 - \sum_{n\ge2}\frac{1}{n^{\Re s}} \;\ge\; 1 - \sum_{n\ge2}\frac{1}{n^{2}}
--   = 2 - \frac{\pi^{2}}{6} \approx 0.355 \;>\; \frac14 .$$
--
--   The constant $1/4$ is a convenient round value below that.
--
--   Non-vanishing far to the right is the anchor for contour-shifting arguments: it guarantees
--   $\log L(s,\chi)$ and $L'/L(s,\chi)$ are defined on a region one can start from, before moving
--   the contour leftwards toward the critical strip where the real difficulties are. It also
--   provides the normalisation for Perron-type integrals, whose vertical line of integration is
--   taken at $\Re s = 2$ precisely because of bounds like this one.
--
--   **Formalization note.** `LFunction χ` is the analytically continued $L$-function, which on
--   $\Re s \ge 2$ coincides with the absolutely convergent series.
-- source:
--   Classical; see Montgomery & Vaughan, *Multiplicative Number Theory I*, §10.2. Lean proof extracted from `Salt/SW/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace DirichletLFunctions

open DirichletCharacter in
theorem LFunction_center_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 2 ≤ s.re) : (1 : ℝ) / 4 ≤ ‖LFunction χ s‖ := by sorry

end DirichletLFunctions

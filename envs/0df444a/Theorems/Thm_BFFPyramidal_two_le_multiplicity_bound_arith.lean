-- Prove2me | Theorems.Thm_BFFPyramidal_two_le_multiplicity_bound_arith
-- name    : BFFPyramidal.two_le_multiplicity_bound_arith
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-13T18:28:25.155976+00:00
-- url     : https://prove2.me/theorems/4cdf49e7-f7f4-47e2-8e06-4913837b35af
-- title:
--   The multiplicity bound is at least two (arithmetic ingredient)
-- statement:
--   For every integer $l \ge 2$,
--   $$ \left\lfloor \frac{P(l)\,\varphi(l)}{l} \right\rfloor + 1 \;\ge\; 2, $$
--   equivalently $P(l)\,\varphi(l) \ge l$, where $P(l)$ is the greatest prime factor of $l$ and $\varphi$ is Euler's totient function.
--
--   This arithmetic inequality is what turns the multiplicity bound of Berger-Felzenbaum-Fraenkel into the Herzog-Schönheim conjecture for pyramidal groups: the bound always forces at least *two* subgroups of equal order. The hypothesis $l \ge 2$ cannot be dropped — at $l = 1$ one has $P(1) = 0$ and the left-hand side is $1$.
--
--   **Formalization note.** This is a statement of pure arithmetic: no group appears in it. It is separated out because it is the ingredient that turns the multiplicity bound into the Herzog-Schönheim conjecture.
--
--    The floor is natural-number division, which truncates, so the statement is `2 ≤ (maxPrimeFac l * Nat.totient l) / l + 1`.
-- source:
--   Berger--Felzenbaum--Fraenkel 1987, Remark on the multiplicity of a partition of a group into cosets, Fund. Math. 128 (1987) 139-144, https://doi.org/10.4064/fm-128-3-139-144, p. 139, the remark following the Theorem ("Note that $x \ge 2$")

import Mathlib
import Definitions.Def_BFFPyramidal_arithmetic

namespace BFFPyramidal

theorem two_le_multiplicity_bound_arith (l : ℕ) (hl : 2 ≤ l) :
    2 ≤ (maxPrimeFac l * Nat.totient l) / l + 1 := by
  sorry

end BFFPyramidal

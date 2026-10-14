-- Prove2me | Theorems.Thm_ClassNumberFormula_pell_four_solvable
-- name    : ClassNumberFormula.pell_four_solvable
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T12:54:46.033264+00:00
-- url     : https://prove2.me/theorems/7bc7258b-0df3-4f95-b392-c6b8c6585d4f
-- title:
--   For a fundamental discriminant $d>0$, $t^2-du^2=4$ has a solution with $t,u>0$
-- statement:
--   Let $d > 0$ be a fundamental discriminant. Then there are positive integers $t, u$ with
--   $$t^2 - d\,u^2 = 4 .$$
--
--   The source takes such a solution, with $u$ minimal, to define $\varepsilon = \frac12(t + u\sqrt d)$; this milestone records that the solution exists, so that $\varepsilon$ is well defined.
-- source:
--   Wikipedia, "Class number formula" (revision oldid=1366411311), https://en.wikipedia.org/w/index.php?title=Class_number_formula&oldid=1366411311, section "Dirichlet class number formula" ("For d > 0, let t > 0, u > 0 be the solution to the Pell equation $t^2 - du^2 = 4$ for which u is smallest")

import Mathlib
import Definitions.Def_ClassNumberFormula_Kronecker
open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real

namespace ClassNumberFormula

theorem pell_four_solvable (d : ℤ) (hd : IsFundamentalDiscriminant d) (hpos : 0 < d) :
    ∃ t u : ℕ, 0 < t ∧ 0 < u ∧ (t : ℤ) ^ 2 - d * (u : ℤ) ^ 2 = 4 := by sorry

end ClassNumberFormula

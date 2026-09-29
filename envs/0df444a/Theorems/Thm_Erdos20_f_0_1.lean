-- Prove2me | Theorems.Thm_Erdos20_f_0_1
-- name    : Erdos20.f_0_1
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T17:24:45.170992+00:00
-- url     : https://prove2.me/theorems/8f7763fd-e93d-43cd-bddb-7296466ead0a
-- title:
--   Sanity check: $f(0,1) = 1$
-- statement:
--   For the sunflower threshold $f(n,k)$ (the least $m$ such that every $n$-uniform family with at least $m$ members contains a $k$-sunflower),
--
--   $$f(0,1) = 1.$$
--
--   This is a test case from the source formalization: one member always forms a $1$-sunflower, while the empty family has none.
-- source:
--   Formal Conjectures, `FormalConjectures/ErdosProblems/20.lean` (Erdős Problem 20), https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/20.lean ; https://www.erdosproblems.com/20 (theorem `f_0_1`)

import Definitions.Def_Erdos20_defs
import Mathlib

namespace Erdos20
theorem f_0_1 : f 0 1 = 1 := by sorry
end Erdos20

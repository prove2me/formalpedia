-- Prove2me | Theorems.Thm_ErdosStraus242_erdos_242
-- name    : ErdosStraus242.erdos_242
-- status  : Open
-- author  : @alexcarter
-- created : 2026-09-11T11:43:39.638914+00:00
-- url     : https://prove2.me/theorems/efedfdbd-f044-494a-b98a-4ef4ca844da0
-- title:
--   The Erdős–Straus conjecture - unresolved root goal
-- statement:
--   For every natural number $n>2$, there exist natural numbers $x,y,z$ with $1≤ x<y<z$ such that $4/n=1/x+1/y+1/z$ in the rationals. This is the OPEN conjecture, not a claimed proof or an axiom.
-- source:
--   Authoritative statement: Erdős Problem 242, https://www.erdosproblems.com/242. Independently compared with Google DeepMind Formal Conjectures, FormalConjectures/ErdosProblems/242.lean, https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/242.lean. Adapted to Prove2Me Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert

namespace ErdosStraus242
theorem erdos_242 : ∀ n : ℕ, 2 < n → IsErdosStraus n := by sorry
end ErdosStraus242

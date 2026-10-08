-- Prove2me | Theorems.Thm_Erdos592_specker_omega_pow_nat_not
-- name    : Erdos592.specker_omega_pow_nat_not
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T18:08:07.814241+00:00
-- url     : https://prove2.me/theorems/bc75f480-8ac4-41ca-b46e-29d43876f7a2
-- title:
--   Specker: $\omega^n\not\to(\omega^n,3)^2$ for $3\le n<\omega$
-- statement:
--   Let $n$ be a natural number with $n\ge 3$. Then $\omega^n$ is **not** a partition ordinal:
--   $$\omega^n \not\to (\omega^n, 3)^2 .$$
--   That is, there is a red/blue colouring of the edges of the complete graph on a well-ordered set of order type $\omega^n$ with no red set of order type $\omega^n$ and no blue triangle.
--
--   This is the negative half of Specker's 1957 theorem: the property of Erdős Problem 592 fails for every finite $\beta\ge 3$.
-- source:
--   T. F. Bloom, Erdős Problem #592, https://www.erdosproblems.com/592 (page last edited 23 January 2026); Lean encoding of the ordinal Ramsey property follows Formal Conjectures, FormalConjecturesForMathlib/SetTheory/Cardinal/SimpleGraph.lean and FormalConjectures/ErdosProblems/592.lean, https://github.com/google-deepmind/formal-conjectures; Specker [Sp57], E. Specker, Teilmengen von Mengen mit Relationen, Comment. Math. Helv. (1957), 302–314

import Mathlib
import Definitions.Def_Erdos592_Defs

open Cardinal Ordinal

universe u

namespace Erdos592
theorem specker_omega_pow_nat_not (n : ℕ) (hn : 3 ≤ n) :
    ¬ OrdinalCardinalRamsey (ω ^ (n : Ordinal.{u})) (ω ^ (n : Ordinal.{u})) 3 := by sorry
end Erdos592

-- Prove2me | Theorems.Thm_Erdos592_specker_omega_sq
-- name    : Erdos592.specker_omega_sq
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:07:35.06999+00:00
-- url     : https://prove2.me/theorems/636ffb31-f940-4d5e-8262-ba55cf7c866d
-- title:
--   Specker: $\omega^2\to(\omega^2,3)^2$
-- statement:
--   The ordinal $\omega^2$ is a partition ordinal:
--   $$\omega^2 \to (\omega^2, 3)^2 .$$
--   That is, for every red/blue colouring of the edges of the complete graph on a well-ordered set of order type $\omega^2$, there is either a set of vertices of order type $\omega^2$ all of whose pairs are red, or three vertices all of whose pairs are blue.
--
--   This is the case $\beta=2$ of Erdős Problem 592, due to Specker (1957).
-- source:
--   T. F. Bloom, Erdős Problem #592, https://www.erdosproblems.com/592 (page last edited 23 January 2026); Lean encoding of the ordinal Ramsey property follows Formal Conjectures, FormalConjecturesForMathlib/SetTheory/Cardinal/SimpleGraph.lean and FormalConjectures/ErdosProblems/592.lean, https://github.com/google-deepmind/formal-conjectures; Specker [Sp57], E. Specker, Teilmengen von Mengen mit Relationen, Comment. Math. Helv. (1957), 302–314

import Mathlib
import Definitions.Def_Erdos592_Defs

open Cardinal Ordinal

universe u

namespace Erdos592
theorem specker_omega_sq : OrdinalCardinalRamsey.{u} (ω ^ 2) (ω ^ 2) 3 := by sorry
end Erdos592

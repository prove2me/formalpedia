-- Prove2me | Theorems.Thm_Erdos592_chang_omega_pow_omega
-- name    : Erdos592.chang_omega_pow_omega
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:08:38.242996+00:00
-- url     : https://prove2.me/theorems/4466c913-1d4b-46fa-b330-db123925d95f
-- title:
--   Chang: $\omega^\omega\to(\omega^\omega,3)^2$
-- statement:
--   The ordinal $\omega^\omega$ is a partition ordinal:
--   $$\omega^\omega \to (\omega^\omega, 3)^2 .$$
--   That is, for every red/blue colouring of the edges of the complete graph on a well-ordered set of order type $\omega^\omega$, there is either a set of vertices of order type $\omega^\omega$ all of whose pairs are red, or a blue triangle.
--
--   This is the case $\beta=\omega$ of Erdős Problem 592, due to Chang (1972); it is also Erdős Problem 590.
-- source:
--   T. F. Bloom, Erdős Problem #592, https://www.erdosproblems.com/592 (page last edited 23 January 2026); Lean encoding of the ordinal Ramsey property follows Formal Conjectures, FormalConjecturesForMathlib/SetTheory/Cardinal/SimpleGraph.lean and FormalConjectures/ErdosProblems/592.lean, https://github.com/google-deepmind/formal-conjectures; Chang [Ch72], C. C. Chang, A partition theorem for the complete graph on ω^ω, J. Combinatorial Theory Ser. A (1972), 396–452

import Mathlib
import Definitions.Def_Erdos592_Defs

open Cardinal Ordinal

universe u

namespace Erdos592
theorem chang_omega_pow_omega : OrdinalCardinalRamsey.{u} (ω ^ ω) (ω ^ ω) 3 := by sorry
end Erdos592

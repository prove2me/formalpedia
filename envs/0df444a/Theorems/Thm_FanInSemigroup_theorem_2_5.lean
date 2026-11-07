-- Prove2me | Theorems.Thm_FanInSemigroup_theorem_2_5
-- name    : FanInSemigroup.theorem_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:38.176458+00:00
-- url     : https://prove2.me/theorems/f05ecf55-03fd-4705-8ef5-392b7e0ea1fa
-- title:
--   Theorem 2.5 [MP] — starfree, rs-accepted and noncounting coincide
-- statement:
--   Let $L$ be a regular language over a finite alphabet that does not contain the empty word. Then the following are equivalent:
--
--   1. $L$ is starfree.
--   2. $L$ is accepted by an rs machine.
--   3. $L$ is noncounting.
--
--   The implication from noncounting to rs machines is the one the main theorem uses. The paper cites the theorem from McNaughton and Papert.
--
--   Differences from the source:
--   - encoding: a regular set, over the finite alphabet of a finite automaton → [Finite α] together with Language.IsRegular; reason: Mathlib's predicate also allows an infinite alphabet, which the page does not consider
--   - encoding: "accepted by an rs machine" with flipflops F1,...,Fk → some machine with m flipflops, m = 0 allowed; reason: a machine with no flipflops accepts all words or none, which a one-flipflop machine does as well
--   - reading: "the state of flipflops F1,...,Fi−1" with no time index → every r_i, s_i reads the state vector from before the current letter (synchronous update); reason: the other reading makes Theorem 2.5 false, on the words whose second-to-last letter is 1
-- source:
--   Chandra, Fortune, Lipton, Unbounded Fan-in Circuits and Associative Functions, STOC 1983, doi:10.1145/800061.808732, Theorem 2.5, p.55

import Definitions.Def_FanInSemigroup_IsNoncounting
import Definitions.Def_FanInSemigroup_StarfreeExp
import Definitions.Def_FanInSemigroup_RSMachine

set_option autoImplicit false

namespace FanInSemigroup

/-- **Theorem 2.5 [MP].** Chandra, Fortune, Lipton, STOC 1983, p.55: "Suppose L is a regular set
not containing the empty string. Then the following are equivalent. 1. L is starfree. 2. L is
accepted by an rs machine. 3. L is noncounting."

**Formalization Note.** The alphabet is finite, as "regular set" and "finite automaton" mean on
pp.54–55; Mathlib's `Language.IsRegular` also allows an infinite alphabet. rs machines update
synchronously (`RSMachine.step`). The paper cites this from McNaughton, Papert. -/
theorem theorem_2_5 {α : Type*} [Finite α] (L : Language α) (hL : L.IsRegular) (hε : [] ∉ L) :
    List.TFAE [IsStarfree L, AcceptedByRS L, IsNoncounting L] := by sorry

end FanInSemigroup

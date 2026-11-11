-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_lemma_3_4
-- name    : FiniteGroupTesting.LinearQuery.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:10:45.794547+00:00
-- url     : https://prove2.me/theorems/0274193b-cb90-448a-8ba4-9b9e860d0641
-- title:
--   Lemma 3.4 — transitivity and doubling
-- statement:
--   Suppose Algorithm 1, with its stated valid transitive old action on $H$, $e\in H$ and $b\notin H$, successfully returns the stored action on $K$. No group law is assumed for the unknown operation. Then the returned images are permutations, $H\subseteq K$, and
--
--   $$P_K\text{ acts transitively on }K,\qquad |K|\ge2|H|.$$
--
--   Both conclusions concern the action actually returned by the procedure. Doubling controls the number of reconstruction stages even on arbitrary input tables.
--
--   Differences from the source:
--   - encoding: [n] = {1,...,n} and its subsets → Fin n with i relabelled i+1, and indexed stored subsets; reason: bijections preserve every table entry, group, and probability; unused ambient labels are fixed by stored permutations
--   - encoding: the queue loop stops upon rejection or an empty queue → at most n queue iterations, with charged inert iterations after stopping; reason: disjoint discovery permits at most n pops; the same queries and output result, and the padding costs only O(n) time
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 17, Lemma 3.4

import Definitions.Def_FiniteGroupTesting_LinearQuery_ActionAssertions

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery
open OracleRun

/-- Lemma 3.4, p. 17, including both transitivity and doubling, without a group-table promise. -/
theorem lemma_3_4 {n : ℕ} (op : Table n) (a : StoredAction n) (e b : Fin n)
    (hinput : ExtensionInput a e b) (r : Outcome n (Option (ExtensionOutput n)))
    (hr : Executes op (exploreExtension a e b) r) (out : ExtensionOutput n)
    (hout : r.value = some out) :
    out.action.Valid ∧ a.domain.carrier ⊆ out.action.domain.carrier ∧
      TransitiveOn out.action.group out.action.domain.carrier ∧
      2 * a.domain.count ≤ out.action.domain.count := by sorry

end FiniteGroupTesting.LinearQuery

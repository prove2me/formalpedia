-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_lemma_3_6
-- name    : FiniteGroupTesting.LinearQuery.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:10:48.729173+00:00
-- url     : https://prove2.me/theorems/39564404-3699-440d-882b-6c51561f75a1
-- title:
--   Lemma 3.6 — honest subgroup extension
-- statement:
--   Let $(G,*)$ be a genuine group, $H\le G$, and let the stored old action be exactly the true left-regular action of $H$. For every $b\notin H$, Algorithm 1 never rejects and returns
--
--   $$K=\langle H,b\rangle_*.$$
--
--   Every returned generator is the restriction to $K$ of a true left translation by an element of $K$, and the returned action is regular. The group multiplication in the statement is exactly the operation used to answer oracle queries. The output is pinned to the actual execution, rather than chosen with the asserted conclusions.
--
--   Differences from the source:
--   - encoding: [n] = {1,...,n} and its subsets → Fin n with i relabelled i+1, and indexed stored subsets; reason: bijections preserve every table entry, group, and probability; unused ambient labels are fixed by stored permutations
--   - encoding: the queue loop stops upon rejection or an empty queue → at most n queue iterations, with charged inert iterations after stopping; reason: disjoint discovery permits at most n pops; the same queries and output result, and the padding costs only O(n) time
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 18–19, Lemma 3.6

import Definitions.Def_FiniteGroupTesting_LinearQuery_ActionAssertions

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery
open OracleRun

/-- Lemma 3.6, pp. 18--19, including no rejection, exact subgroup, translations, regularity. -/
theorem lemma_3_6 {n : ℕ} [Group (Fin n)] (H : Subgroup (Fin n))
    (a : StoredAction n) (ha : a.Valid) (hH : (a.domain.carrier : Set (Fin n)) = H)
    (hleft : TrueLeftAction H a.group) (b : Fin n) (hb : b ∉ H)
    (r : Outcome n (Option (ExtensionOutput n)))
    (hr : Executes (fun x y : Fin n => x * y) (exploreExtension a 1 b) r) :
    ∃ out : ExtensionOutput n, r.value = some out ∧ out.action.Valid ∧
      (out.action.domain.carrier : Set (Fin n)) =
        (Subgroup.closure ((H : Set (Fin n)) ∪ {b}) : Set (Fin n)) ∧
      (∀ i < out.action.degree, ∃ z ∈ out.action.domain.carrier,
        ∀ x ∈ out.action.domain.carrier, out.action.image i x = z * x) ∧
      RegularOn out.action.group out.action.domain.carrier := by sorry

end FiniteGroupTesting.LinearQuery

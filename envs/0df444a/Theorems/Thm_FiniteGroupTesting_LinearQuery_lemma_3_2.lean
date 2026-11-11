-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_lemma_3_2
-- name    : FiniteGroupTesting.LinearQuery.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:11:51.920483+00:00
-- url     : https://prove2.me/theorems/d97dc8e4-8bd0-45d3-b714-af28c35e99fd
-- title:
--   Lemma 3.2 — block invariant
-- statement:
--   Let $H$ carry the valid stored transitive permutation action supplied to Algorithm 1, with $e\in H$ and fixed $b\notin H$. At every completed queue stage actually reached on an arbitrary total input operation, if no rejection has occurred, then
--
--   $$D=\bigsqcup_{t\in T}C_t,\qquad C_t=\mu_t(H),\qquad \mu_t:H\longrightarrow C_t\text{ is bijective},\qquad\mu_t(e)=t.$$
--
--   This is the block invariant for genuine execution prefixes, including initialization; it is not a condition assumed of arbitrary records.
--
--   Differences from the source:
--   - encoding: [n] = {1,...,n} and its subsets → Fin n with i relabelled i+1, and indexed stored subsets; reason: bijections preserve every table entry, group, and probability; unused ambient labels are fixed by stored permutations
--   - encoding: the queue loop stops upon rejection or an empty queue → at most n queue iterations, with charged inert iterations after stopping; reason: disjoint discovery permits at most n pops; the same queries and output result, and the padding costs only O(n) time
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 16, Lemma 3.2

import Definitions.Def_FiniteGroupTesting_LinearQuery_ActionAssertions

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery
open OracleRun

/-- Lemma 3.2, p. 16, at actual completed loop stages, not arbitrary stored records. -/
theorem lemma_3_2 {n : ℕ} (op : Table n) (a : StoredAction n) (e b : Fin n)
    (hinput : ExtensionInput a e b) (j : ℕ) (hj : j ≤ n)
    (r : Outcome n (ExtensionState n)) (hr : Executes op (extensionPrefix a e b j) r)
    (hnot : r.value.rejected = false) : BlockPartition a e r.value := by sorry

end FiniteGroupTesting.LinearQuery

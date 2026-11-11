-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_lemma_3_7
-- name    : FiniteGroupTesting.LinearQuery.lemma_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:11:12.430294+00:00
-- url     : https://prove2.me/theorems/282396b8-dd58-4a65-b834-d10cf87400ca
-- title:
--   Lemma 3.7 — certified group extension
-- statement:
--   Suppose the old action $P_H$ is regular, Algorithm 1 returns $K$, and its returned action $P_K$ is regular. Define $\circ_H$ and $\circ_K$ from these actual actions and the distinguished label $e$. Then
--
--   $$H\le(K,\circ_K),\qquad x\circ_Hy=x\circ_Ky\quad(x,y\in H),\qquad K=\langle H,b\rangle_{\circ_K}.$$
--
--   The formal assertion includes the group axioms on $K$, subgroup closure for $H$, agreement of the two constructed laws and the complete generated-subgroup equality. Regularity is assumed here exactly as in this lemma, and is never silently assumed in the whole tester.
--
--   Differences from the source:
--   - encoding: [n] = {1,...,n} and its subsets → Fin n with i relabelled i+1, and indexed stored subsets; reason: bijections preserve every table entry, group, and probability; unused ambient labels are fixed by stored permutations
--   - encoding: the queue loop stops upon rejection or an empty queue → at most n queue iterations, with charged inert iterations after stopping; reason: disjoint discovery permits at most n pops; the same queries and output result, and the padding costs only O(n) time
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 19, Lemma 3.7

import Definitions.Def_FiniteGroupTesting_LinearQuery_ActionAssertions

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery
open OracleRun

/-- Lemma 3.7, p. 19: subgroup, agreement of both constructed laws, generated subgroup. -/
theorem lemma_3_7 {n : ℕ} (op : Table n) (a : StoredAction n) (e b : Fin n)
    (hinput : ExtensionInput a e b) (hold : RegularOn a.group a.domain.carrier)
    (r : Outcome n (Option (ExtensionOutput n)))
    (hr : Executes op (exploreExtension a e b) r) (out : ExtensionOutput n)
    (hout : r.value = some out) (hnew : RegularOn out.action.group out.action.domain.carrier) :
    let oldLaw := inducedLaw a.group e
    let newLaw := inducedLaw out.action.group e
    GroupLawOn newLaw e out.action.domain.carrier ∧
      (a.domain.carrier ⊆ out.action.domain.carrier ∧ SubgroupFor newLaw e a.domain.carrier) ∧
      (∀ x ∈ a.domain.carrier, ∀ y ∈ a.domain.carrier, oldLaw x y = newLaw x y) ∧
      ∀ x : Fin n, x ∈ out.action.domain.carrier ↔
        Generated newLaw e ((a.domain.carrier : Set (Fin n)) ∪ {b}) x := by sorry

end FiniteGroupTesting.LinearQuery

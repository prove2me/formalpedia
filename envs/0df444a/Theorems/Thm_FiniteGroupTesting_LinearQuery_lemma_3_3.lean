-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_lemma_3_3
-- name    : FiniteGroupTesting.LinearQuery.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:10:54.472559+00:00
-- url     : https://prove2.me/theorems/fd29e21c-e76b-49be-973c-ef46cc5f3f0f
-- title:
--   Lemma 3.3 — the old action embeds
-- statement:
--   At any nonrejected reached stage of Algorithm 1, let $P_H$ be the old permutation group and $D$ the discovered set with charts $\mu_t$. There is an injective homomorphism
--
--   $$P_H\hookrightarrow\operatorname{Sym}(D),\qquad q\mapsto\widehat q,\qquad\widehat q|_{C_t}=\mu_tq\mu_t^{-1}.$$
--
--   Each restriction is a permutation of its block, and the combined map permutes $D$. For every old generator $\gamma$, its image obeys exactly the stored-copy formula $\widehat\gamma(\mu_t(c))=\mu_t(\gamma(c))$. Ambient unused labels are fixed, so the ambient permutation encoding restricts faithfully to $D$.
--
--   Differences from the source:
--   - encoding: [n] = {1,...,n} and its subsets → Fin n with i relabelled i+1, and indexed stored subsets; reason: bijections preserve every table entry, group, and probability; unused ambient labels are fixed by stored permutations
--   - encoding: the queue loop stops upon rejection or an empty queue → at most n queue iterations, with charged inert iterations after stopping; reason: disjoint discovery permits at most n pops; the same queries and output result, and the padding costs only O(n) time
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 17, Lemma 3.3

import Definitions.Def_FiniteGroupTesting_LinearQuery_ActionAssertions

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery
open OracleRun

/-- Lemma 3.3, p. 17: blockwise conjugation, permutation restrictions, embedding,
and agreement with Algorithm 1's generator formula. -/
theorem lemma_3_3 {n : ℕ} (op : Table n) (a : StoredAction n) (e b : Fin n)
    (hinput : ExtensionInput a e b) (j : ℕ) (hj : j ≤ n)
    (r : Outcome n (ExtensionState n)) (hr : Executes op (extensionPrefix a e b j) r)
    (hnot : r.value.rejected = false) :
    ∃ φ : a.group →* Equiv.Perm (Fin n), Function.Injective φ ∧
      (∀ q : a.group, ∀ x, φ q x = blockLift r.value q.val x) ∧
      (∀ q : a.group, Set.BijOn (φ q)
        (r.value.discovered.carrier : Set (Fin n)) (r.value.discovered.carrier : Set (Fin n))) ∧
      (∀ q : a.group, ∀ t ∈ r.value.representatives.carrier,
        Set.BijOn (φ q) (blockSet a r.value t : Set (Fin n)) (blockSet a r.value t : Set (Fin n))) ∧
      ∀ q : a.group, ∀ i < a.degree, q.val = storedPermutation (a.image i) →
        ∀ t ∈ r.value.representatives.carrier, ∀ c ∈ a.domain.carrier,
          φ q (r.value.chart t c) = r.value.chart t (a.image i c) := by sorry

end FiniteGroupTesting.LinearQuery

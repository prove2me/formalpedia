-- Prove2me | Theorems.Thm_EdmondsPartition_Main_only_if_part
-- name    : EdmondsPartition.Main.only_if_part
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:24:55.447237+00:00
-- url     : https://prove2.me/theorems/43506460-3c96-4bfc-996c-e486f3b1d814
-- title:
--   THEOREM 1, "only if", §1.3, p. 69 — for any independence system, a partition into k independent sets forces |A| ≤ k·r(A)
-- statement:
--   Let $M$ be a finite set with a family of independent subsets satisfying Axiom 1 only (every subset of an independent set is independent), an *independence system*, and let $r(A)$ be the largest cardinality of an independent subset of $A$. If $M$ is partitioned into $k$ independent sets $I_1,\dots,I_k$, then for every $A\subseteq M$,
--   $$|A|\le\sum_{i=1}^k|I_i\cap A|\le k\cdot r(A).$$
--
--   This is the easy half of THEOREM 1, and it holds without Axiom 2.
--
--   **Formalization Note** Only Axiom 1 is assumed; Axiom 2 and the non-emptiness of the family are dropped, which makes the statement stronger than the matroid case. The hypothesis is the partition of THEOREM 1 (disjoint parts covering $M$, empty parts allowed); disjointness is not needed for the inequality but is kept so that the statement composes with the goal.
-- source:
--   Edmonds, Minimum partition of a matroid into independent subsets, J. Res. NBS 69B (1965), p. 69, §1.3, the "only if" part of THEOREM 1

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates
import Definitions.Def_EdmondsPartition_Main_Basic

namespace EdmondsPartition.Main

open WhitneyMatroid.RankIndep

theorem only_if_part {α : Type*} [Fintype α] [DecidableEq α] (Indep : Finset α → Prop)
    (h1 : IndepI1 Indep) :
    ∀ (k : ℕ) (I : Fin k → Finset α), IsPartitionInto Indep k I →
      ∀ A : Finset α, (A.card : ℤ) ≤ (k : ℤ) * rankOfIndep Indep A := by sorry

end EdmondsPartition.Main

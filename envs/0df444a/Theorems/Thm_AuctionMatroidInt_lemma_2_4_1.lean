-- Prove2me | Theorems.Thm_AuctionMatroidInt_lemma_2_4_1
-- name    : AuctionMatroidInt.lemma_2_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:26:01.797576+00:00
-- url     : https://prove2.me/theorems/92e166ea-99f5-47fc-875f-0960bac2da67
-- title:
--   Lemma 2.4 (1) — binary search with independence queries
-- statement:
--   There is an absolute constant $C$ with the following property. Let $E$ be a finite set, $w\in\mathbb R^E$, $T\subseteq S\subseteq E$ and $v\in E\setminus S$. There is a deterministic algorithm, given $w,S,T,v$, that for every matroid $M=(E,\mathcal I)$ with $S\in\mathcal I$, using only the independence oracle of $M$:
--
--   1. returns an element $u\in T$ with $S+v-u\in\mathcal I$ and $w(u)\le w(u')$ for every $u'\in T$ with $S+v-u'\in\mathcal I$, whenever such an element exists, and reports that none exists otherwise;
--   2. makes at most $C\log(|T|+2)$ independence queries.
--
--   This is the binary search technique of Nguyễn and of Chakrabarty, Lee, Sidford, Singla and Wong; it is the subroutine behind the $O(\log r)$-query price computation (Lemma 5.14) and the $O(\log r)$-query check of Line 7 of Algorithm 4 (Lemma 5.15). The paper states it without proof.
--
--   **Formalization Note** The algorithm is a `QueryTree Unit α (Option α)` built from $(w,S,T,v)$; $C$ is chosen before the ground set; $S+v-u$ is `(insert v S).erase u`.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset α → Prop on a finite type α (ground set = α); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
--   - encoding: an algorithm using O(log |T|) independence queries → ∃ C (absolute, before α) and a QueryTree built from (w, S, T, v) whose queries are ≤ C · log(|T| + 2) on the oracle of every matroid with S ∈ I; reason: the query model of §2.1: the matroid is seen only through its oracle and computation is free
--   - reading: find u … (if such an element exists) → returns some u with the stated property, and none only when no such u exists; reason: the proof of Lemma 5.15 uses the algorithm to conclude that no desired element exists (p.30); reporting non-existence costs at most one query
--   - reading: O(log |T|) → C · log(|T| + 2); reason: log |T| ≤ 0 for |T| ≤ 1 while |T| = 1 may need a query; the two agree up to a constant factor for |T| ≥ 2
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Lemma 2.4 (1), p.11 (PDF p.13)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_AuctionMatroidInt_QueryTree

namespace AuctionMatroidInt

/-- **Lemma 2.4 (1) (binary search technique, independence queries).**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Lemma 2.4 (1), p.11:
"Let M = (E, I) be a matroid and let w ∈ ℝ^E be a weight function. Let S ∈ I, T ⊆ S, and
v ∈ E \ S. Then … (1) Using O(log |T|) independence queries, we can find an element u ∈ T
minimizing w(u) subject to S + v − u ∈ I (if such an element exists)."

There is an absolute constant `C` such that for every finite ground set `α`, every weight `w`,
every `T ⊆ S` and `v ∉ S` there is a deterministic query algorithm (a `QueryTree` built from
`w, S, T, v`) which, for **every** matroid `I` with `S ∈ I`, returns `some u` with `u ∈ T`,
`S + v − u ∈ I` and `w(u)` minimal among such elements, returns `none` only when no such element
exists, and makes at most `C · log(|T| + 2)` independence queries.

**Formalization Note.** The matroid is reached only through `indepOracle`. "(if such an element
exists)" is read as also reporting non-existence (`none`), which the proof of Lemma 5.15 uses
("we conclude that no desired element exists", p.30). `log |T|` is read as `log(|T| + 2)`, since
`|T| = 1` still needs a query. `S + v − u` is `(insert v S).erase u`. -/
theorem lemma_2_4_1 :
    ∃ C : ℝ, ∀ {α : Type} [Fintype α] [DecidableEq α] (w : α → ℝ) (S T : Finset α) (v : α),
      T ⊆ S → v ∉ S →
      ∃ A : QueryTree Unit α (Option α), ∀ I : Finset α → Prop,
        CombOpt.MatroidPolytope.IsMatroid I → I S →
        (∀ u, A.run (indepOracle fun _ => I) = some u →
          u ∈ T ∧ I ((insert v S).erase u) ∧
            ∀ u' ∈ T, I ((insert v S).erase u') → w u ≤ w u') ∧
        (A.run (indepOracle fun _ => I) = none → ∀ u ∈ T, ¬ I ((insert v S).erase u)) ∧
        (A.queries (indepOracle fun _ => I) : ℝ) ≤ C * Real.log (T.card + 2) := by sorry

end AuctionMatroidInt

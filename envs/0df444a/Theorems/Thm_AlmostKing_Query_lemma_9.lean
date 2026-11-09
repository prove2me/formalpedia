-- Prove2me | Theorems.Thm_AlmostKing_Query_lemma_9
-- name    : AlmostKing.Query.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:54.320227+00:00
-- url     : https://prove2.me/theorems/6bb07744-ae8f-4c14-8173-13488ea125d4
-- title:
--   Lemma 9 — a powerful vertex in the courts
-- statement:
--   For every $0<\tau<1$, there is a choice of $\eta$ with $0<\eta\le\min\{\tau,1/16\}$ such that the following holds. Let $R$ be a loopless asymmetric directed graph on $r$ indices, with
--   $$r\ge\lceil1/\eta\rceil,\qquad |\{\{i,j\}:i\ne j,\ i\not\to j,\ j\not\to i\}|\le\eta r^2.$$
--   Let $A_1,\ldots,A_r$ be disjoint finite courts of common size $L\ge1/\eta$. For every tournament $S$ on $Q=\bigcup_i A_i$, there is $w\in Q$ such that
--   $$|N_R^+(I_S(w))|\ge(1-2\tau)r,\qquad I_S(w)=\{i:|N_S^+(w)\cap A_i|\ge\lceil\eta L\rceil\}.$$
--
--   The parameter $\eta$ is chosen before the graph, courts, and tournament. This is the court reachability statement used for selecting the output vertex.
--
--   Differences from the source:
--   - generalization: the group graph and courts from Lemma 7 → any oriented $R$ and pairwise disjoint equal-sized courts satisfying the index lower bound, missing-pair bound, and court-size lower bound; reason: these are exactly the properties used in the proof on pp. 10–11; every output of Lemma 7 satisfies them
--   - encoding: a tournament with vertex set $Q$ → a digraph on a finite ambient type that is a tournament when restricted to $Q$; reason: all court counts and the output use only vertices in $Q$, so arcs outside $Q$ are irrelevant
--   - encoding: $[n]=\{1,\ldots,n\}$ → $\mathrm{Fin}\,n=\{0,\ldots,n-1\}$; reason: relabeling by an order-preserving bijection preserves all graph and counting conditions
-- source:
--   Ziad Ismaili Alaoui, Oded Lachish, Nikhil S. Mande, A King for Almost Everyone, STOC 2027 submission #472 (October 2026), SHA-256 c262b203b2088dcae48025a77e016df4cc78f93c1856a6fac580c7577d8dea92, Lemma 9, p. 7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/472.pdf

import Mathlib
import Definitions.Def_AlmostKing_Query_Regularity

namespace AlmostKing.Query

/-- Lemma 9, p. 7, using exactly the oriented-graph and court properties used on pp. 10–11. -/
theorem lemma_9 : ∀ τ : ℝ, 0 < τ → τ < 1 →
    ∃ η : ℝ, 0 < η ∧ η ≤ min τ ((1 : ℝ) / 16) ∧
    ∀ (V : Type) [Fintype V] (r L : ℕ) (R : Digraph (Fin r)),
      IsOriented R → ⌈1 / η⌉₊ ≤ r →
      (missingPairs R : ℝ) ≤ η * (r : ℝ)^2 →
    ∀ A : Fin r → Finset V,
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) →
      (∀ i, (A i).card = L) → 1 / η ≤ (L : ℝ) →
    ∀ S : Digraph V, IsTournamentOn S (courtUnion A) →
      ∃ w ∈ courtUnion A,
        (1 - 2 * τ) * r ≤ (outNbhdSet R (activeGroups S A η L w)).card := by sorry

end AlmostKing.Query

-- Prove2me | Theorems.Thm_AuctionMatroidInt_lemma_2_2
-- name    : AuctionMatroidInt.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:26:21.529965+00:00
-- url     : https://prove2.me/theorems/c85156c4-c439-40ae-869f-75d557e8dd4a
-- title:
--   Lemma 2.2 — gross substitutes property
-- statement:
--   Let $M=(E,\mathcal I)$ be a matroid and $S\subseteq E$. Let $p,p'\in\mathbb R^E$ satisfy
--
--   $$
--   p(e)\le p'(e)\ \ (e\in E),\qquad p(e)=p'(e)\ \ (e\in S).
--   $$
--
--   If $S$ is contained in a $p$-minimum base of $M$, then $S$ is also contained in a $p'$-minimum base of $M$.
--
--   In the analysis of Algorithm 3 this is applied with $p=-q^*$ and $p'=-q$ to show that, at the beginning of every round, $X$ is contained in a $q$-maximum base of $M_1$ (Lemma 5.4).
--
--   **Formalization Note** The ground set is a finite type `α`; $p$-minimum bases are `IsMinBase`.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset α → Prop on a finite type α (ground set = α); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Lemma 2.2, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_AuctionMatroidInt_IsMaxBase

namespace AuctionMatroidInt

/-- **Lemma 2.2 (gross substitutes property).**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Lemma 2.2, p.11:
"Let M = (E, I) be a matroid and let S ⊆ E. Let p, p′ ∈ ℝ^E be vectors such that p(e) ≤ p′(e)
for all e ∈ E, and p(e) = p′(e) for all e ∈ S. If S is contained in a p-minimum base of M, then
it is also contained in a p′-minimum base of M."

**Formalization Note.** The matroid is the published `CombOpt.MatroidPolytope.IsMatroid`
predicate on `Finset α`, with ground set the finite type `α`; p-minimum bases are `IsMinBase`. -/
theorem lemma_2_2 {α : Type*} [Fintype α] [DecidableEq α] (I : Finset α → Prop)
    (hI : CombOpt.MatroidPolytope.IsMatroid I) (S : Finset α) (p p' : α → ℝ)
    (hle : ∀ e, p e ≤ p' e) (heq : ∀ e ∈ S, p e = p' e)
    (hS : ∃ B, IsMinBase I p B ∧ S ⊆ B) :
    ∃ B, IsMinBase I p' B ∧ S ⊆ B := by sorry

end AuctionMatroidInt

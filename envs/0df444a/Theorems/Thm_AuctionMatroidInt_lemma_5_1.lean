-- Prove2me | Theorems.Thm_AuctionMatroidInt_lemma_5_1
-- name    : AuctionMatroidInt.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:26:53.76869+00:00
-- url     : https://prove2.me/theorems/7048b3e0-abc5-46de-a310-176d43dd7b61
-- title:
--   Lemma 5.1 — contraction of the maximum base utility
-- statement:
--   Let $M=(E,\mathcal I)$ be a matroid with base family $\mathcal B$, $0<\varepsilon<1$, and let $q,q'\in\Lambda^E$ where $\Lambda=\{0\}\cup\{(1+\varepsilon)^k:k\in\mathbb Z\}$. Let $Y\subseteq E$ be contained in a $q$-maximum base of $M$, and suppose
--
--   1. (H1) $q'(e)\le q(e)$ for every $e\in E$;
--   2. (H2) $q'(e)\le q(e)/(1+\varepsilon)$ for every $e\in E\setminus Y$ such that $Y+e$ is contained in a $q$-maximum base.
--
--   Then
--
--   $$
--   \max_{B\in\mathcal B}q'(B)-q(Y)\le\frac{1}{1+\varepsilon}\Bigl(\max_{B\in\mathcal B}q(B)-q(Y)\Bigr).
--   $$
--
--   Applied to $M_1$ with $q=q^*$ and $q'$ the utilities at the end of a round, it shows that the utility part of $U$ shrinks by a factor $1+\varepsilon$ outside the proposal (Lemma 5.7).
--
--   **Formalization Note** $\Lambda$ membership is `InLambda ε`; $\max_{B\in\mathcal B}$ is `maxBaseWeight`.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset α → Prop on a finite type α (ground set = α); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Lemma 5.1, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_weight
import Definitions.Def_AuctionMatroidInt_IsMaxBase
import Definitions.Def_AuctionMatroidInt_maxBaseWeight
import Definitions.Def_AuctionMatroidInt_roundUp

namespace AuctionMatroidInt

/-- **Lemma 5.1.**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Lemma 5.1, p.20:
"Let M = (E, I) be a matroid with base family 𝓑, let q, q′ ∈ Λ^E, and let Y ⊆ E be contained in
a q-maximum base of M. Suppose that (H1) q′(e) ≤ q(e) for every e ∈ E, and (H2)
q′(e) ≤ q(e)/(1 + ε) for every e ∈ E \ Y such that Y + e is contained in a q-maximum base. Then
max_{B∈𝓑} q′(B) − q(Y) ≤ (1/(1 + ε)) (max_{B∈𝓑} q(B) − q(Y))."

**Formalization Note.** `Λ = {0} ∪ {(1+ε)^k | k ∈ ℤ}` is `InLambda ε`; `0 < ε < 1` is the
paper's standing range of ε (§2.1, p.10). `max_{B∈𝓑}` is `maxBaseWeight`. -/
theorem lemma_5_1 {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (I : Finset α → Prop) (hI : CombOpt.MatroidPolytope.IsMatroid I) (q q' : α → ℝ)
    (hq : ∀ e, InLambda ε (q e)) (hq' : ∀ e, InLambda ε (q' e)) (Y : Finset α)
    (hY : ∃ B, IsMaxBase I q B ∧ Y ⊆ B)
    (H1 : ∀ e, q' e ≤ q e)
    (H2 : ∀ e, e ∉ Y → (∃ B, IsMaxBase I q B ∧ insert e Y ⊆ B) → q' e ≤ q e / (1 + ε)) :
    maxBaseWeight I q' - CombOpt.MatroidPolytope.weight q Y ≤
      1 / (1 + ε) * (maxBaseWeight I q - CombOpt.MatroidPolytope.weight q Y) := by sorry

end AuctionMatroidInt

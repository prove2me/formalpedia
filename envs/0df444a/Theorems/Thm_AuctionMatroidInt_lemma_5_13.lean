-- Prove2me | Theorems.Thm_AuctionMatroidInt_lemma_5_13
-- name    : AuctionMatroidInt.lemma_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:26:36.593051+00:00
-- url     : https://prove2.me/theorems/e9eef5e4-c8cd-4433-b72d-d1dd03d92b6b
-- title:
--   Lemma 5.13 — checking Line 6 through a maintained maximum base
-- statement:
--   Let $M_1$ be a matroid with base family $\mathcal B_1$ and $q\in\mathbb R^E$. Suppose $Y\subseteq E$ is contained in a $q$-maximum base $Z$ of $M_1$, and let $e\in E\setminus Y$. The following are equivalent:
--
--   1. there exists $e'\in Z\setminus Y$ such that $Z-e'+e\in\mathcal B_1$ and $q(e')=q(e)$;
--   2. $Y+e$ is contained in a $q$-maximum base of $M_1$.
--
--   In the paper $q=q^*$. The lemma shows that Algorithm 4, which maintains $Z$ and tests condition 1, behaves exactly as Algorithm 3, which tests condition 2.
--
--   **Formalization Note** $Z-e'+e$ is `insert e (Z.erase e')` (equal to $Z$ when $e'=e$); $\mathcal B_1$ is `IsBasisOf I₁ Finset.univ`.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset α → Prop on a finite type α (ground set = α); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
--   - generalization: q* (the utility vector induced by X*, π*, with values in Λ) and M₁ loopless → any q : α → ℝ and any matroid M₁; reason: the proof uses only that Z is a q*-maximum base and the simultaneous exchange property; q = q* and a loopless M₁ give the source's statement
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Lemma 5.13, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_IsBasisOf
import Definitions.Def_AuctionMatroidInt_IsMaxBase

namespace AuctionMatroidInt

/-- **Lemma 5.13 (checking Line 6 through a maintained maximum base).**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Lemma 5.13, p.28:
"Suppose that Y ⊆ E is contained in a q*-maximum base Z of M₁, and let e ∈ E \ Y. Then, the
following are equivalent: (i) There exists e′ ∈ Z \ Y such that Z − e′ + e ∈ 𝓑₁ and
q*(e′) = q*(e). (ii) Y + e is contained in a q*-maximum base of M₁."

**Formalization Note.** Stated for every matroid `M₁` and every weight vector `q : α → ℝ` in the
role of `q*`. `Z − e′ + e` is `insert e (Z.erase e')` (equal to `Z` when `e′ = e`), and `𝓑₁` is
`IsBasisOf I₁ Finset.univ`. -/
theorem lemma_5_13 {α : Type*} [Fintype α] [DecidableEq α] (I₁ : Finset α → Prop)
    (hI₁ : CombOpt.MatroidPolytope.IsMatroid I₁) (q : α → ℝ) (Y Z : Finset α)
    (hZ : IsMaxBase I₁ q Z) (hYZ : Y ⊆ Z) (e : α) (he : e ∉ Y) :
    (∃ e' ∈ Z \ Y, CombOpt.MatroidPolytope.IsBasisOf I₁ Finset.univ (insert e (Z.erase e')) ∧
        q e' = q e) ↔
      ∃ B, IsMaxBase I₁ q B ∧ insert e Y ⊆ B := by sorry

end AuctionMatroidInt

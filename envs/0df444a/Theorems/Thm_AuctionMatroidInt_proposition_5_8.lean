-- Prove2me | Theorems.Thm_AuctionMatroidInt_proposition_5_8
-- name    : AuctionMatroidInt.proposition_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:59.58451+00:00
-- url     : https://prove2.me/theorems/f93ba7d0-a871-44a9-bba9-b15a13b09a66
-- title:
--   Proposition 5.8 — Algorithm 3 is a $(1-3\varepsilon)$-approximation
-- statement:
--   Assume $M_1,M_2$ are loopless matroids on a finite set $E$, $w(e)>0$ for all $e$, and $0<\varepsilon<1$. Let $r_1(E)$ be the rank of $M_1$ and
--
--   $$
--   T\ \ge\ \Bigl\lceil 10\bigl(\varepsilon^{-1}\log r_1(E)+\varepsilon^{-2}\bigr)\Bigr\rceil
--   $$
--
--   (natural logarithm). Then every set $X$ returned by Algorithm 3 with $T$ rounds (any scan order, tie-break and maximizer) is a common independent set with
--
--   $$
--   w(X)\ge(1-3\varepsilon)\,w(\mathrm{OPT}_w).
--   $$
--
--   Run with $\varepsilon/3$, this gives the approximation guarantee of Theorem 1.3.
--
--   **Formalization Note** $r_1(E)$ is the published `CombOpt.MatroidPolytope.rank I₁ Finset.univ`; the bound is against every common independent set. For $\varepsilon\ge1/3$ the guarantee is trivial.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset α → Prop on a finite type α (ground set = α); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
--   - generalization: the standing assumptions of §2.1 (pp.10–11): 1/ε is an integer, M₁, M₂ have no loops, w > 0, r_i(E) ≤ 2r (and 1/ε ≤ n+1 for unit weights) → only: M₁, M₂ loopless matroids, w > 0, 0 < ε < 1; reason: the proofs in §5 never use 1/ε ∈ ℤ or r_i(E) ≤ 2r; adding them back gives the source's statement as a special case
--   - generalization: T := ⌈10 (ε⁻¹ log(r₁(E)) + ε⁻²)⌉ rounds → every T ≥ ⌈10 (ε⁻¹ log r₁(E) + ε⁻²)⌉; reason: the proof derives T < 10 (ε⁻¹ log r₁(E) + ε⁻²) from a failure of the guarantee, so it applies to every larger T; T equal to the ceiling is the source's case
--   - encoding: the set X returned by Algorithm 3 → every X with IsAlg3Output (every run, scan order, tie-break and maximizer); reason: the paper's scan order and tie-break are arbitrary
--   - encoding: π(e) = ⊥ for e ∉ X → π : α → ℝ, read only on X by every definition; reason: values of π off X never influence p̄, p, q, U, π(X) or a step; same executions
--   - encoding: w(OPT_w) for a maximum-weight common independent set OPT_w → the bound against w(Y) for every common independent Y; reason: equivalent, since OPT_w maximizes w over common independent sets (which exist: ∅)
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Proposition 5.8, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_weight
import Definitions.Def_CombOpt_MatroidPolytope_rank
import Definitions.Def_AuctionMatroidInt_Loopless
import Definitions.Def_AuctionMatroidInt_IsAlg3Output

namespace AuctionMatroidInt

/-- **Proposition 5.8 (approximation ratio of Algorithm 3).**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Proposition 5.8, p.26:
"Let T := ⌈10 (ε⁻¹ log(r₁(E)) + ε⁻²)⌉. Then, Algorithm 3 returns a common independent set X with
w(X) ≥ (1 − 3ε) w(OPT_w)." Here "log denotes the natural logarithm" (p.21).

Under the standing assumptions (§2.1, pp.10–11: `M₁, M₂` loopless matroids, `w > 0`,
`0 < ε < 1`), for every number of rounds `T ≥ ⌈10 (ε⁻¹ log r₁(E) + ε⁻²)⌉` and every output
`X` of every run of Algorithm 3 with `T` rounds (any scan order, tie-break and maximizer), `X`
is common independent and `(1 − 3ε) w(Y) ≤ w(X)` for every common independent `Y`.

**Formalization Note.** `r₁(E)` is the published `CombOpt.MatroidPolytope.rank I₁ Finset.univ`;
the logarithm is `Real.log` (natural). `r₁(E) = 0` only when the ground set is empty (no loops),
where `Real.log 0 = 0` is harmless. The number of rounds may exceed the paper's `T` (the proof
derives `T < 10 (ε⁻¹ log r₁(E) + ε⁻²)` from a failure of the guarantee). -/
theorem proposition_5_8 {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (w : α → ℝ) (hw : ∀ e, 0 < w e) (I₁ I₂ : Finset α → Prop)
    (hI₁ : CombOpt.MatroidPolytope.IsMatroid I₁) (hI₂ : CombOpt.MatroidPolytope.IsMatroid I₂)
    (hL₁ : Loopless I₁) (hL₂ : Loopless I₂) (T : ℕ)
    (hT : ⌈10 * (ε⁻¹ * Real.log (CombOpt.MatroidPolytope.rank I₁ Finset.univ : ℝ) + ε⁻¹ ^ 2)⌉₊
      ≤ T)
    (X : Finset α) (hX : IsAlg3Output ε w I₁ I₂ T X) :
    I₁ X ∧ I₂ X ∧ ∀ Y : Finset α, I₁ Y → I₂ Y →
      (1 - 3 * ε) * CombOpt.MatroidPolytope.weight w Y ≤ CombOpt.MatroidPolytope.weight w X := by sorry

end AuctionMatroidInt

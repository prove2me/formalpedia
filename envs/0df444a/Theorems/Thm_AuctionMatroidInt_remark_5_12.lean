-- Prove2me | Theorems.Thm_AuctionMatroidInt_remark_5_12
-- name    : AuctionMatroidInt.remark_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:31:05.520921+00:00
-- url     : https://prove2.me/theorems/1dacac6f-b742-4847-adfd-c99a020a78a3
-- title:
--   Remark 5.12 — unit weights: $O(\varepsilon^{-2})$ rounds suffice
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $M_1,M_2$ be loopless matroids on a finite set $E$ with $r_1(E)\le 2r$, where $r$ is the maximum size of a common independent set, let $0<\varepsilon<1$, and let all weights be $1$. If $T\ge C\varepsilon^{-2}$, then every set $X$ returned by Algorithm 3 with $T$ rounds is a common independent set with
--
--   $$
--   |X|\ge(1-3\varepsilon)\,r .
--   $$
--
--   In the unit-weight setting the bound $g_0\le U_0<2r$ replaces $g_0<r_1(E)\cdot\mathrm{opt}$, which removes the $\varepsilon^{-1}\log r_1(E)$ term; this gives the unit-weight query bound of Theorem 1.3.
--
--   **Formalization Note** $w\equiv1$ is `fun _ => 1`, so $w(X)=|X|$; $C$ is chosen before the ground set and the matroids; the bound is stated against every common independent set.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset α → Prop on a finite type α (ground set = α); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
--   - generalization: the standing assumptions of §2.1: 1/ε is an integer, M₁, M₂ have no loops, r_i(E) ≤ 2r for i ∈ {1, 2}, 1/ε ≤ n + 1 (unit weights) → only: M₁, M₂ loopless, r₁(E) ≤ 2r, 0 < ε < 1; reason: the argument uses only r₁(E) ≤ 2r (for U₀ < 2r) among the size assumptions; adding the others gives the source's statement
--   - reading: “the same argument shows that the number of iterations can be reduced to T = O(ε⁻²)” → the conclusion of Proposition 5.8 (common independent output with |X| ≥ (1 − 3ε) r) for T rounds; reason: the remark re-runs the proof of Proposition 5.8 with a smaller T
--   - generalization: T = O(ε⁻²) rounds → ∃ C > 0 (absolute), every T ≥ C ε⁻²; reason: the argument applies to every larger T; T = ⌈C ε⁻²⌉ is the source's case
--   - encoding: π(e) = ⊥ for e ∉ X → π : α → ℝ, read only on X by every definition; reason: values of π off X never influence p̄, p, q, U, π(X) or a step; same executions
--   - encoding: w(OPT_w) for a maximum-weight common independent set OPT_w → the bound against w(Y) for every common independent Y; reason: equivalent, since OPT_w maximizes w over common independent sets (which exist: ∅)
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Remark 5.12, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_rank
import Definitions.Def_AuctionMatroidInt_Loopless
import Definitions.Def_AuctionMatroidInt_maxCommonCard
import Definitions.Def_AuctionMatroidInt_IsAlg3Output

namespace AuctionMatroidInt

/-- **Remark 5.12 (unit weights: O(ε⁻²) rounds suffice).**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Remark 5.12, p.28:
"For the unit-weight setting, we have the stronger bound g₀ ≤ U₀ = max_{B∈𝓑₁} q(B) < 2r = 2·opt.
Using this bound, the same argument shows that the number of iterations can be reduced to
T = O(ε⁻²)."

There is an absolute constant `C > 0` such that, under the standing assumptions (§2.1,
pp.10–11: `M₁, M₂` loopless matroids, `0 < ε < 1`, and `r₁(E) ≤ 2r` with `r` the maximum size of
a common independent set), with unit weights `w ≡ 1` and any number of rounds `T ≥ C ε⁻²`,
every output `X` of every run of Algorithm 3 is common independent and
`|X| ≥ (1 − 3ε)|Y|` for every common independent `Y`.

**Formalization Note.** The conclusion is that of Proposition 5.8 (which the remark's "the same
argument" re-proves); with `w ≡ 1`, `w(X) = |X|`. `C` is chosen before the ground set and the
matroids. -/
theorem remark_5_12 :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : Type} [Fintype α] [DecidableEq α] (ε : ℝ), 0 < ε → ε < 1 →
      ∀ I₁ I₂ : Finset α → Prop,
        CombOpt.MatroidPolytope.IsMatroid I₁ → CombOpt.MatroidPolytope.IsMatroid I₂ →
        Loopless I₁ → Loopless I₂ →
        CombOpt.MatroidPolytope.rank I₁ Finset.univ ≤ 2 * maxCommonCard I₁ I₂ →
        ∀ T : ℕ, C / ε ^ 2 ≤ T →
        ∀ X : Finset α, IsAlg3Output ε (fun _ => 1) I₁ I₂ T X →
          I₁ X ∧ I₂ X ∧ ∀ Y : Finset α, I₁ Y → I₂ Y →
            (1 - 3 * ε) * (Y.card : ℝ) ≤ X.card := by sorry

end AuctionMatroidInt

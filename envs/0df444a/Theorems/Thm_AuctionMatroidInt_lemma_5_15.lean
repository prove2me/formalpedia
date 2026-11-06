-- Prove2me | Theorems.Thm_AuctionMatroidInt_lemma_5_15
-- name    : AuctionMatroidInt.lemma_5_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:27:06.287142+00:00
-- url     : https://prove2.me/theorems/f1cf5361-3fb8-4730-84f6-175747e9bc83
-- title:
--   Lemma 5.15 — checking Line 7 of Algorithm 4 with $O(\log r)$ queries
-- statement:
--   There is an absolute constant $C$ with the following property. Let $E$ be finite, $0<\varepsilon<1$, $w>0$, $X^*\subseteq E$ with prices $\pi^*$, $Z,Y\subseteq E$, $e\in E$, and let $q_Z$ be a vector. There is a deterministic algorithm, given these data, that for all loopless matroids $M_1,M_2$ on $E$ such that $X^*\in\mathcal I_2$, $Z$ is a $q^*$-maximum base of $M_1$ ($q^*$ the utility vector induced by $X^*,\pi^*$), $Y\subseteq Z$, $e\notin Y$ and $q_Z=q^*$ on $Z$:
--
--   1. finds $e'\in Z\setminus Y$ with $Z-e'+e\in\mathcal I_1$ and $q^*(e')=q^*(e)$ if such $e'$ exists, and reports that none exists otherwise;
--   2. makes at most $C\log(|X^*|+|Z|+2)$ independence queries to $M_1$ and $M_2$.
--
--   In Algorithm 4, $|X^*|\le r$ and $|Z|=r_1(E)\le 2r$, so the bound is $O(\log r)$.
--
--   **Formalization Note** The algorithm is a `QueryTree (Fin 2) α (Option α)` ($0\mapsto M_1$, $1\mapsto M_2$); the vector $q_Z$ models that "the algorithm explicitly maintains $q^*$-values of all elements in $Z$" (p.30); $Z-e'+e$ is `insert e (Z.erase e')`.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset α → Prop on a finite type α (ground set = α); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
--   - encoding: π(e) = ⊥ for e ∉ X → π : α → ℝ, read only on X by every definition; reason: values of π off X never influence p̄, p, q, U, π(X) or a step; same executions
--   - encoding: an algorithm using O(log r) independence queries → ∃ C (absolute, before α) and a QueryTree built from (ε, w, X*, π*, Z, Y, e, q_Z); reason: the query model of §2.1; the q*-values on Z are explicit data of Algorithm 4 (p.30)
--   - generalization: “in Line 7 of Algorithm 4” with O(log r) queries → every X* ∈ I₂, π*, every q*-maximum base Z ⊇ Y and e ∉ Y, with C · log(|X*| + |Z| + 2) queries; reason: in Line 7, X* is common independent (|X*| ≤ r), Z is a q*-maximum base containing Y (|Z| = r₁(E) ≤ 2r) and e ∉ Y, so the bound specializes to O(log r)
--   - reading: find e′ … if such e′ exists → returns some e′ with the property, and none only when no such e′ exists; reason: the proof concludes “that no desired element exists” (p.30)
--   - reading: O(log r) → a bound with log(· + 2); reason: log r ≤ 0 for r ≤ 1; the two agree up to a constant factor for arguments ≥ 2
--   - generalization: the standing assumptions 1/ε ∈ ℤ and r_i(E) ≤ 2r of §2.1 → not assumed; reason: the procedure does not use them; adding them gives the source's statement
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Lemma 5.15, pp.29–30 (PDF pp.31–32)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_AuctionMatroidInt_Loopless
import Definitions.Def_AuctionMatroidInt_QueryTree
import Definitions.Def_AuctionMatroidInt_IsMaxBase
import Definitions.Def_AuctionMatroidInt_utility

namespace AuctionMatroidInt

/-- **Lemma 5.15 (checking Line 7 of Algorithm 4 with few queries).**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Lemma 5.15, p.29:
"In Line 7 of Algorithm 4, for e ∈ E \ Y, we can find e′ ∈ Z \ Y such that Z − e′ + e ∈ I₁ and
q*(e′) = q*(e) using O(log r) independence queries if such e′ exists."

There is an absolute constant `C` such that for every finite ground set `α`, every `0 < ε < 1`,
every `w > 0`, every `X*`, `π*`, `Z`, `Y`, `e` and every vector `qZ` there is a deterministic query
algorithm with oracles for `M₁` (`0`) and `M₂` (`1`), built from these data, such that for all
loopless matroids `M₁, M₂` with `X* ∈ I₂`, `Z` a `q*`-maximum base of `M₁` (`q*` the utility induced
by `X*, π*`), `Y ⊆ Z`, `e ∉ Y` and `qZ = q*` on `Z` (the algorithm "explicitly maintains q*-values of
all elements in Z", p.30): it returns `some e′` with `e′ ∈ Z \ Y`, `Z − e′ + e ∈ I₁` and
`q*(e′) = q*(e)`, it returns `none` only if no such `e′` exists, and it makes at most
`C · log(|X*| + |Z| + 2)` independence queries.

**Formalization Note.** The matroids are reached only through `indepOracle`. "if such e′
exists" is read as also reporting non-existence (`none`), as the proof does (p.30). The bound is
in `|X*|` and `|Z|`: in Algorithm 4, `|X*| ≤ r` and `|Z| = r₁(E) ≤ 2r` (§2.1), so it is
`O(log r)` there; `log` is read as `log(· + 2)`. `Z − e′ + e` is `insert e (Z.erase e')`. -/
theorem lemma_5_15 :
    ∃ C : ℝ, ∀ {α : Type} [Fintype α] [DecidableEq α] (ε : ℝ) (w : α → ℝ) (Xs : Finset α)
      (πs : α → ℝ) (Z Y : Finset α) (e : α) (qZ : α → ℝ), 0 < ε → ε < 1 → (∀ a, 0 < w a) →
      ∃ A : QueryTree (Fin 2) α (Option α), ∀ I : Fin 2 → Finset α → Prop,
        CombOpt.MatroidPolytope.IsMatroid (I 0) → CombOpt.MatroidPolytope.IsMatroid (I 1) →
        Loopless (I 0) → Loopless (I 1) → I 1 Xs →
        IsMaxBase (I 0) (utility ε w (I 1) Xs πs) Z → Y ⊆ Z → e ∉ Y →
        (∀ z ∈ Z, qZ z = utility ε w (I 1) Xs πs z) →
        (∀ e', A.run (indepOracle I) = some e' →
          e' ∈ Z \ Y ∧ I 0 (insert e (Z.erase e')) ∧
            utility ε w (I 1) Xs πs e' = utility ε w (I 1) Xs πs e) ∧
        (A.run (indepOracle I) = none →
          ¬ ∃ e' ∈ Z \ Y, I 0 (insert e (Z.erase e')) ∧
            utility ε w (I 1) Xs πs e' = utility ε w (I 1) Xs πs e) ∧
        (A.queries (indepOracle I) : ℝ) ≤ C * Real.log (Xs.card + Z.card + 2) := by sorry

end AuctionMatroidInt

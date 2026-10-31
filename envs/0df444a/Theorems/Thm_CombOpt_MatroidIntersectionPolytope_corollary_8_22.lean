-- Prove2me | Theorems.Thm_CombOpt_MatroidIntersectionPolytope_corollary_8_22
-- name    : CombOpt.MatroidIntersectionPolytope.corollary_8_22
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:41:36.700008+00:00
-- url     : https://prove2.me/theorems/9adb5b26-5d8f-478b-aeb4-2737c6527138
-- title:
--   Corollary 8.22 — a common independent set optimal for both parts of a weight-splitting
-- statement:
--   Let $M_1=(S,\mathcal I_1)$ and $M_2=(S,\mathcal I_2)$ be matroids on $S$ and $c\in\mathbb R^S$. A pair $c^1,c^2\in\mathbb R^S$ is a **weight-splitting** for $c$ if $c=c^1+c^2$. There exist a common independent set $J$ and a weight-splitting $c^1,c^2$ for $c$ such that, for $i=1$ and $2$, $J$ is $c^i$-optimal in $\mathcal I_i$:
--
--   $$
--   c^i(J)\ \ge\ c^i(J')\quad\text{for every } J'\in\mathcal I_i .
--   $$
--
--   Any such $J$ is a maximum-weight common independent set, since $c(J)=c^1(J)+c^2(J)\ge c^1(J')+c^2(J')=c(J')$ for every common independent $J'$; the corollary says this certificate always exists.
--
--   Differences from the source:
--   - encoding: a matroid (S, I): S a finite set, I a family of subsets of S satisfying (M0)–(M2); r(A) the size of a basis of A → S a finite type, subsets Finset S, I the predicate FinMatroid.Indep with the axioms (M0)–(M2) as fields; r(A) the largest size of an independent subset of A; reason: same objects: by (M2) the largest independent subset of A has the size of every basis of A
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.5, Corollary 8.22, p. 299 (PDF p. 306)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsWeightOptimal

namespace CombOpt.MatroidIntersectionPolytope

/-- **Corollary 8.22** (weight splitting).
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.5, Corollary 8.22, p. 299 (PDF p. 306): "There exist a common independent set J and a
weight-splitting c¹, c² for c such that J is cⁱ-optimal in Iᵢ for i = 1 and 2." Here "Call a pair
c¹, c² of vectors a weight-splitting for c if c = c¹ + c²" (p. 299).

For matroids `M₁, M₂` on `S` and every `c ∈ ℝ^S` there are `J ⊆ S` independent in both and
`c¹, c² ∈ ℝ^S` with `c = c¹ + c²` such that `J` has maximum `c¹`-weight among the independent
sets of `M₁` and maximum `c²`-weight among the independent sets of `M₂`. -/
theorem corollary_8_22 {S : Type*} [Fintype S] [DecidableEq S] (M₁ M₂ : FinMatroid S)
    (c : S → ℝ) :
    ∃ (J : Finset S) (c₁ c₂ : S → ℝ), M₁.Indep J ∧ M₂.Indep J ∧ c = c₁ + c₂ ∧
      IsWeightOptimal M₁ c₁ J ∧ IsWeightOptimal M₂ c₂ J := by sorry

end CombOpt.MatroidIntersectionPolytope

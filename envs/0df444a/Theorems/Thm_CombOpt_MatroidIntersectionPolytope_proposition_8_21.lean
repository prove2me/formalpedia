-- Prove2me | Theorems.Thm_CombOpt_MatroidIntersectionPolytope_proposition_8_21
-- name    : CombOpt.MatroidIntersectionPolytope.proposition_8_21
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:42:48.809507+00:00
-- url     : https://prove2.me/theorems/6c70aca3-e74b-4df2-a714-6695a37c29ff
-- title:
--   Proposition 8.21 — an optimal dual of (8.8) splits into optimal duals of the two single-matroid problems
-- statement:
--   Let $M_1,M_2$ be matroids on $S$ with rank functions $r_1,r_2$, and let $c\in\mathbb R^S$. Choose an optimal solution $(\bar y^1,\bar y^2)$ of the dual program
--
--   $$
--   \min\Big\{\sum_{A\subseteq S}\big(r_1(A)y^1_A+r_2(A)y^2_A\big) : \sum_{A\ni e}(y^1_A+y^2_A)\ge c_e\ (e\in S),\ y^1,y^2\ge0\Big\}.\qquad(8.8)
--   $$
--
--   Define $c^1_e=\sum(\bar y^1_A : A\subseteq S,\ e\in A)$ for $e\in S$ and $c^2=c-c^1$, and let Problem $i$ be the single-matroid dual (8.2) for $M_i$ and $c^i$: minimize $\sum_A r_i(A)y_A$ subject to $\sum_{A\ni e}y_A\ge c^i_e$ for all $e$ and $y\ge0$. Then:
--
--   1. for $i=1,2$, $\bar y^i$ is optimal to Problem $i$;
--   2. conversely, if $y^i$ is optimal to Problem $i$ for $i=1$ and $2$, then $(y^1,y^2)$ is optimal to (8.8).
--
--   The second part is used in the proofs of Theorems 8.19 and 8.20; the first gives the weight-splitting form of the optimality conditions (Corollary 8.22).
--
--   **Formalization Note** The statement holds for every optimal $(\bar y^1,\bar y^2)$ of (8.8); the existence of one is not part of the proposition.
--
--   Differences from the source:
--   - encoding: a matroid (S, I): S a finite set, I a family of subsets of S satisfying (M0)–(M2); r(A) the size of a basis of A → S a finite type, subsets Finset S, I the predicate FinMatroid.Indep with the axioms (M0)–(M2) as fields; r(A) the largest size of an independent subset of A; reason: same objects: by (M2) the largest independent subset of A has the size of every basis of A
--   - reading: Choose an optimal solution (ȳ¹, ȳ²) of (8.8) → for every optimal (ȳ¹, ȳ²) of (8.8); reason: the proposition is about an arbitrary chosen optimal solution
--   - reading: (8.2): Σ(y_A : e ∈ A ⊆ S) ≥ c_e, for all e ∈ E → the constraint for every e ∈ S; reason: the ground set of the chapter is S; E is a misprint
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.5, Proposition 8.21, p. 299 (PDF p. 306), with (8.2), p. 279 (PDF p. 286)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_rank
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_coverSum
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsOptimal82
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsOptimal88

namespace CombOpt.MatroidIntersectionPolytope

/-- **Proposition 8.21** (splitting an optimal dual solution of (8.8)).
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.5, Proposition 8.21, p. 299 (PDF p. 306), with the setup preceding it: "Choose an
optimal solution (ȳ¹, ȳ²) of (8.8). Define c¹, c² ∈ ℝ^S as follows. Let
c¹_e = Σ(ȳ¹(A) : A ⊆ S, e ∈ A) for all e ∈ S, and let c² = c − c¹. Let Problem i denote (8.2)
where c is replaced by cⁱ and M is replaced by Mᵢ, for i = 1 and 2. … Proposition 8.21 For
i = 1 and 2, ȳⁱ is optimal to Problem i. Conversely, if yⁱ is optimal to Problem i for i = 1
and 2, then (y¹, y²) is optimal to (8.8)."

For every optimal `(ȳ¹, ȳ²)` of (8.8), with `c¹ = coverSum ȳ¹` and `c² = c − c¹`: `ȳ¹` is optimal
for (8.2) with `(M₁, c¹)`, `ȳ²` is optimal for (8.2) with `(M₂, c²)`, and every pair
`(y¹, y²)` with `yⁱ` optimal for (8.2) with `(Mᵢ, cⁱ)` is optimal for (8.8).

**Formalization Note.** The statement is universally quantified over the chosen optimal solution
`(ȳ¹, ȳ²)`; its existence is not part of the proposition. -/
theorem proposition_8_21 {S : Type*} [Fintype S] [DecidableEq S] (M₁ M₂ : FinMatroid S)
    (c : S → ℝ) (ybar₁ ybar₂ : Finset S → ℝ) (hopt : IsOptimal88 M₁ M₂ c (ybar₁, ybar₂)) :
    (IsOptimal82 M₁ (coverSum ybar₁) ybar₁ ∧ IsOptimal82 M₂ (c - coverSum ybar₁) ybar₂) ∧
      ∀ y₁ y₂ : Finset S → ℝ, IsOptimal82 M₁ (coverSum ybar₁) y₁ →
        IsOptimal82 M₂ (c - coverSum ybar₁) y₂ → IsOptimal88 M₁ M₂ c (y₁, y₂) := by sorry

end CombOpt.MatroidIntersectionPolytope

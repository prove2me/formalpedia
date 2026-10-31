-- Prove2me | Theorems.Thm_CombOpt_MatroidIntersectionPolytope_theorem_8_19
-- name    : CombOpt.MatroidIntersectionPolytope.theorem_8_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:42:29.500852+00:00
-- url     : https://prove2.me/theorems/c4aea3cd-f138-4fc3-b268-5b3248cef290
-- title:
--   Theorem 8.19 — a common independent set maximizes $c^Tx$ over (8.7)
-- statement:
--   Let $M_1=(S,\mathcal I_1)$ and $M_2=(S,\mathcal I_2)$ be matroids on the same finite set $S$ with rank functions $r_1,r_2$. For every $c\in\mathbb R^S$ there is a common independent set $J\in\mathcal I_1\cap\mathcal I_2$ whose characteristic vector $\chi_J$ maximizes $c^Tx$ subject to
--
--   $$
--   x(A)\le r_1(A),\quad x(A)\le r_2(A)\quad(A\subseteq S),\qquad x\ge0.\qquad(8.7)
--   $$
--
--   That is, $\chi_J$ satisfies (8.7) and $c^T\chi_J\ge c^Tx$ for all $x$ satisfying (8.7). In particular, the maximum weight of a common independent set equals the linear-programming maximum over (8.7) (Edmonds, 1970).
--
--   Differences from the source:
--   - encoding: a matroid (S, I): S a finite set, I a family of subsets of S satisfying (M0)–(M2); r(A) the size of a basis of A → S a finite type, subsets Finset S, I the predicate FinMatroid.Indep with the axioms (M0)–(M2) as fields; r(A) the largest size of an independent subset of A; reason: same objects: by (M2) the largest independent subset of A has the size of every basis of A
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.5, Theorem 8.19, p. 298 (PDF p. 305)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_rank
import Definitions.Def_CombOpt_TJoin_charVec
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_intersectionLP

namespace CombOpt.MatroidIntersectionPolytope

/-- **Theorem 8.19** (Edmonds 1970).
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.5, Theorem 8.19, p. 298 (PDF p. 305): "For every c ∈ ℝ^S there is a common independent
set J whose characteristic vector maximizes cᵀx subject to (8.7)."

For matroids `M₁, M₂` on `S` and every `c ∈ ℝ^S` there is `J` independent in both matroids whose
characteristic vector lies in (8.7) and has `cᵀχ_J ≥ cᵀx` for every `x` satisfying (8.7). -/
theorem theorem_8_19 {S : Type*} [Fintype S] [DecidableEq S] (M₁ M₂ : FinMatroid S)
    (c : S → ℝ) :
    ∃ J : Finset S, M₁.Indep J ∧ M₂.Indep J ∧ CombOpt.TJoin.charVec J ∈ intersectionLP M₁ M₂ ∧
      ∀ x ∈ intersectionLP M₁ M₂, ∑ e, c e * x e ≤ ∑ e, c e * CombOpt.TJoin.charVec J e := by sorry

end CombOpt.MatroidIntersectionPolytope

-- Prove2me | Theorems.Thm_CombOpt_MatroidIntersectionPolytope_theorem_8_4
-- name    : CombOpt.MatroidIntersectionPolytope.theorem_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:42:28.257785+00:00
-- url     : https://prove2.me/theorems/5a48803e-518f-437e-be95-0ed053431e1c
-- title:
--   Theorem 8.4 — the greedy solution is optimal for the matroid linear program (8.1)
-- statement:
--   Let $(S,\mathcal I)$ be a matroid with rank function $r$, let $c\in\mathbb R^S$, and let $x^0$ be the characteristic vector of a set $J$ found by the Greedy Algorithm. Then $x^0$ is an optimal solution of
--
--   $$
--   \max\Big\{\sum_{e\in S}c_ex_e : x(A)\le r(A)\ \text{for all } A\subseteq S,\ x\ge0\Big\}.\qquad(8.1)
--   $$
--
--   That is, $x^0$ satisfies (8.1) and $c^Tx^0\ge c^Tx$ for every $x$ satisfying (8.1). This is Edmonds' strengthening of the correctness of the Greedy Algorithm; it is the single-matroid case on which the weighted matroid intersection results build.
--
--   Differences from the source:
--   - encoding: a matroid (S, I): S a finite set, I a family of subsets of S satisfying (M0)–(M2); r(A) the size of a basis of A → S a finite type, subsets Finset S, I the predicate FinMatroid.Indep with the axioms (M0)–(M2) as fields; r(A) the largest size of an independent subset of A; reason: same objects: by (M2) the largest independent subset of A has the size of every basis of A
--   - reading: the set J found by the Greedy Algorithm → every J returned by some run of the Greedy Algorithm (IsGreedyOutput, any tie-breaking); reason: the algorithm says "choose such e with c_e maximum" without fixing ties; the theorem holds for whichever choice is made
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.1, Theorem 8.4, p. 278 (PDF p. 285)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_FinMatroid
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_rank
import Definitions.Def_CombOpt_TJoin_charVec
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_matroidLP
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsGreedyOutput

namespace CombOpt.MatroidIntersectionPolytope

/-- **Theorem 8.4** (Edmonds 1970).
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.1, Theorem 8.4, p. 278 (PDF p. 285): "Let (S, I) be a matroid with rank function r,
let c ∈ ℝ^S, and let x⁰ be the characteristic vector of the set J found by the Greedy Algorithm.
Then x⁰ is an optimal solution of (8.1)."

For every set `J` returned by a run of the Greedy Algorithm (any tie-breaking), its
characteristic vector is feasible for (8.1) and maximizes `Σ_e c_e x_e` over (8.1). -/
theorem theorem_8_4 {S : Type*} [Fintype S] [DecidableEq S] (M : FinMatroid S) (c : S → ℝ)
    (J : Finset S) (hJ : IsGreedyOutput M c J) :
    CombOpt.TJoin.charVec J ∈ matroidLP M ∧
      ∀ x ∈ matroidLP M, ∑ e, c e * x e ≤ ∑ e, c e * CombOpt.TJoin.charVec J e := by sorry

end CombOpt.MatroidIntersectionPolytope

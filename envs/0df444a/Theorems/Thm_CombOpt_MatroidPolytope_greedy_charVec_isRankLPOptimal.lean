-- Prove2me | Theorems.Thm_CombOpt_MatroidPolytope_greedy_charVec_isRankLPOptimal
-- name    : CombOpt.MatroidPolytope.greedy_charVec_isRankLPOptimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:09:33.751689+00:00
-- url     : https://prove2.me/theorems/c37bf5b6-5d89-4c1c-b312-18be03b5db97
-- title:
--   Theorem 8.4 — the characteristic vector of the greedy set is an optimal solution of the rank LP (8.1)
-- statement:
--   Let $(S,\mathcal I)$ be a matroid with rank function $r$, let $c\in\mathbb R^S$, and let $x^0$ be the characteristic vector of a set $J$ returned by the Greedy Algorithm. Then $x^0$ is an optimal solution of the linear program
--   $$\text{maximize } \sum_{e\in S}c_e x_e \quad\text{subject to}\quad x(A)\le r(A)\ \ (A\subseteq S),\qquad x_e\ge 0\ \ (e\in S). \tag{8.1}$$
--
--   This strengthens Theorem 8.2 (the LP relaxation has no better fractional solution) and is due to Edmonds (1970); the Matroid Polytope Theorem 8.5 follows from it.
--
--   Differences from the source:
--   - reading: "the set J found by the Greedy Algorithm" → any set returned by some run of the nondeterministic algorithm; reason: ties are broken arbitrarily (p. 274); the statement for every run is the stronger reading
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 8.4 and (8.1), p. 278 (PDF p. 285)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_IsGreedyOutput
import Definitions.Def_CombOpt_MatroidPolytope_IsRankLPOptimal
import Definitions.Def_OnlineCRS_Combine_indicatorVec

namespace CombOpt.MatroidPolytope

/-- **Theorem 8.4: the greedy set is an optimal solution of the rank LP (Edmonds 1970).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 8.4, p. 278 (PDF p. 285): "Let (S, I) be a matroid with rank function r, let
c ∈ R^S, and let x⁰ be the characteristic vector of the set J found by the Greedy Algorithm. Then
x⁰ is an optimal solution of (8.1)", where (8.1) is "Maximize Σ(c_e x_e : e ∈ S) subject to
x(A) ≤ r(A), for all A ⊆ S; x_e ≥ 0, for all e ∈ S."

For a matroid `I` on a finite ground set, any weights `c`, and any set `J` the Greedy Algorithm
can return, the characteristic vector of `J` is an optimal solution of (8.1).

**Formalization Note.** As in Theorem 8.2, the statement holds for every run of the algorithm.
The characteristic vector of `J` is the published `OnlineCRS.Combine.indicatorVec J`. -/
theorem greedy_charVec_isRankLPOptimal {α : Type*} [Fintype α] [DecidableEq α]
    (I : Finset α → Prop) (hI : IsMatroid I) (c : α → ℝ) (J : Finset α)
    (hJ : IsGreedyOutput I c J) :
    IsRankLPOptimal I c (OnlineCRS.Combine.indicatorVec J) := by sorry

end CombOpt.MatroidPolytope

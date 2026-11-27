-- Prove2me | Theorems.Thm_DynamicOnlineLP_DLA_Supplement_surplus_rule_differs_le
-- name    : DynamicOnlineLP.DLA.Supplement.surplus_rule_differs_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T03:10:26.008674+00:00
-- url     : https://prove2.me/theorems/c9d612f4-8597-4a7a-806b-d480818e9e6b
-- title:
--   Lemma 8 — an optimal primal solution and the surplus rule at an optimal dual price differ at no more than m arrivals
-- statement:
--   Let $S$ be a finite set of arrivals, each with $k$ options, let $f_{tj}$ be the reward and $g_{itj}$ the consumption of resource $i\in\{1,\dots,m\}$ by option $j$ of arrival $t$, and let $d\in\mathbb R^m$. Consider the packing program
--
--   $$\max\ \sum_{t\in S}f_t^{\top}x_t\quad\text{s.t.}\quad\sum_{t\in S}g_{it}^{\top}x_t\le d_i\ (i=1,\dots,m),\qquad x_t\ge0,\quad e^{\top}x_t\le1 .$$
--
--   Assume general position: for every $p\in\mathbb R^m$, at most $m$ arrivals of $S$ have a nonunique maximizer among the score $0$ of rejection and the $k$ surpluses $f_{tj}-\sum_ip_ig_{itj}$. Let $x^*$ be any optimal primal solution and $p^*$ the price part of any optimal dual solution. For each $t\in S$ let $x_t(p^*)$ be $0$ if every surplus at $p^*$ is at most zero and otherwise $e_r$ for any option $r$ of largest surplus, with ties broken arbitrarily. Then
--
--   $$\#\{t\in S:\ x^*_t\ne x_t(p^*)\}\le m .$$
--
--   Whole decision vectors are compared, so the bound is $m$ arrivals and not $mk$ coordinates. Unlike Lemma 1 of the scalar model, no coordinatewise domination $x_t(p^*)\le x^*_t$ is claimed.
--
--   The lemma is used in the proof of Theorem 3: it shows that decisions taken from a learned price consume, up to $m$ units, what the optimal solution of the learning program consumes.
--
--   **Formalization Note** The tie choices form an arbitrary function from arrivals to allowed choices. Taking $S=\{1,\dots,n\}$ and $d=b$ gives the printed lemma, and taking a prefix and a scaled capacity gives the form used by the algorithm.
--
--   Differences from the source:
--   - reading: Lemma 8 carries endnote 4 (at most m arrivals with "ties in f_tj − Σ_i p_i g_itj" for any p), and its proof in Appendix D.1 also lists the equation f_tj − p^T g_tj = 0 → the general-position hypothesis counts the arrivals at which the maximum among the zero score of rejection and the k surpluses is attained twice; reason: this is the tie that D.1 uses; without the tie with rejection the lemma fails for k = 1, three identical arrivals f = g = 1 and b = 2. Excluded are degenerate inputs with more than m tied arrivals at some price, which the paper handles by random perturbation
--   - reading: "the optimal primal and dual solutions" x* and p*, with ties broken arbitrarily → every optimal primal solution, every price part of an optimal dual solution and every allowed choice at each arrival; reason: neither optimum nor the maximizer need be unique
--   - generalization: program (15) on all n arrivals, with f ≥ 0, g in [0,1], right-hand side b, and the lower bound on B of Theorem 3 mentioned before the lemma → any finite set of arrivals, real data f, g and d, and no lower bound on the right-hand side; reason: the proof in D.1 uses none of these restrictions, and the algorithm needs the lemma on prefix programs with scaled capacities
--   - generalization: Appendix D.1's list of tie equations: two equal option surpluses f_tj − p^T g_tj = f_tl − p^T g_tl, or an option surplus equal to 0, at any level → only arrivals whose largest score among rejection (0) and the k surpluses is attained twice are counted; reason: a tie below the largest score changes neither the optimal block decision of (D1) nor the allocation rule; every such counted arrival satisfies one of D.1's equations, so every input in the source's general position satisfies this hypothesis, and the statement covers more inputs
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 886, Lemma 8 (proof: p. 889, Appendix D.1; assumption: p. 889, endnote 4)

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_SimplexPackingLP
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_SurplusRule
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_GeneralPosition

namespace DynamicOnlineLP.DLA.Supplement

open Classical in
/-- Lemma 8 (Agrawal–Wang–Ye 2014, p. 886), on any finite set `S` of arrivals: under general
position, for every optimal primal solution `x*` and every optimal dual resource price `p*` of
the simplex packing LP, and for every way of breaking ties, the vectors `x*_t` and `x_t(p*)`
differ at no more than `m` arrivals. -/
theorem surplus_rule_differs_le {ι : Type} {m k : ℕ} (S : Finset ι) (f : ι → Fin k → ℝ)
    (g : ι → Fin m → Fin k → ℝ) (d : Fin m → ℝ) (x : ι → Fin k → ℝ) (p : Fin m → ℝ)
    (c : ι → Option (Fin k))
    (hGP : BlockGeneralPositionOn S f g)
    (hx : IsBlockPrimalOptimal S f g d x)
    (hp : IsBlockOptimalPrice S f g d p)
    (hc : ∀ t ∈ S, IsSurplusChoice (f t) (g t) p (c t)) :
    (S.filter (fun t => x t ≠ choiceVec (c t))).card ≤ m := by sorry

end DynamicOnlineLP.DLA.Supplement
